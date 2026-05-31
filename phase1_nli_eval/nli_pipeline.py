"""Phase 1 NLI evaluation pipeline.

Single CLI entry point. Loads one of the 5 datasets via data.loaders, runs an
LLM under a chosen prompting technique and prompt language, normalises the
response to a canonical Result, and writes a per-combination JSON results file.
"""

from __future__ import annotations

import argparse
import json
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable

from dotenv import load_dotenv
from rich.progress import BarColumn, MofNCompleteColumn, Progress, SpinnerColumn, TextColumn, TimeElapsedColumn

from clients.azure import assert_env, call_llm, get_client
from clients.models import MODELS
from data.loaders import load_dataset
from data.schema import LANGUAGES, MULTILABEL_SOURCES, Sample, dump_entry, parse_response
from phase1_nli_eval.concurrency import MAX_CONCURRENCY, RPM_PER_DEPLOYMENT, call_with_backoff, get_limiter
from phase1_nli_eval.prompts import build_prompt, select_examples

load_dotenv()

RESULTS_DIR = Path(__file__).resolve().parent / "results"

DATASETS = {"fracas", "fracas-translated", "fracas-extended", "fracas-multilabel", "oyxoy"}

TECHNIQUES = ("zero-shot", "few-shot", "cot")
FLUSH_EVERY = 10
MAX_TOKENS = 800
FEW_SHOT_K = 3
MAX_RETRIES = 3


def _results_path(dataset_key: str, model_key: str, technique: str, language: str) -> Path:
    return RESULTS_DIR / dataset_key / f"{dataset_key}__{model_key}__{technique}__{language}.json"


def _now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _new_state(dataset_key: str, model_key: str, technique: str, language: str, multilabel: bool) -> dict:
    dataset_language = "en" if dataset_key == "fracas" else "el"
    return {
        "metadata": {
            "dataset": dataset_key,
            "model": model_key,
            "technique": technique,
            "language": language,
            "crosslingual": language != dataset_language,
            "multilabel": multilabel,
            "started_at": _now_iso(),
            "completed_at": None,
        },
        "results": [],
    }


def summarize_results(results: list[dict]) -> dict:
    total = len(results)
    llm_error = sum(1 for e in results if isinstance(e.get("raw"), str) and e["raw"].startswith("<LLM call failed"))
    parse_fail = sum(1 for e in results if e.get("predicted") is None) - llm_error
    success_count = sum(1 for e in results if e.get("success") == 1)
    accuracy = success_count / total if total else None
    return {
        "total": total,
        "parse_fail": parse_fail,
        "llm_error": llm_error,
        "success_count": success_count,
        "accuracy": accuracy,
    }


def _flush(path: Path, state: dict) -> None:
    state["summary"] = summarize_results(state["results"])
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")


def run(
    dataset_key: str,
    model_key: str,
    technique: str,
    language: str,
    resume: bool,
    limit: int | None = None,
    on_progress: Callable[[], None] | None = None,
    concurrency: int = MAX_CONCURRENCY,
    rpm: int = RPM_PER_DEPLOYMENT,
) -> int:
    multilabel = dataset_key in MULTILABEL_SOURCES
    provider = MODELS[model_key]["provider"]
    assert_env(provider)
    client = get_client(model_key)
    deployment = MODELS[model_key]["deployment"]

    samples = load_dataset(dataset_key)
    path = _results_path(dataset_key, model_key, technique, language)

    if resume and path.exists():
        state = json.loads(path.read_text(encoding="utf-8"))
        results_by_id = {e["id"]: e for e in state["results"]}
        completed = {eid for eid, e in results_by_id.items() if e.get("predicted") is not None}
    else:
        state = _new_state(dataset_key, model_key, technique, language, multilabel)
        results_by_id = {}
        completed = set()

    pending = [s for s in samples if s.id not in completed]
    if limit is not None:
        pending = pending[:limit]
    total, skipped = len(samples), len(samples) - len(pending)
    print(
        f"[run] dataset={dataset_key} model={model_key} technique={technique} "
        f"language={language} multilabel={multilabel} total={total} skipped(resume)={skipped}"
    )

    limiter = get_limiter(deployment, rpm)
    lock = threading.Lock()
    completed_count = [0]
    pool = samples if technique == "few-shot" else []

    def _process(sample: Sample, progress_cb: Callable[[], None] | None) -> None:
        examples = select_examples(sample, pool, k=FEW_SHOT_K) if technique == "few-shot" else None
        messages = build_prompt(sample, technique, language, multilabel, examples=examples)
        raw, parsed = "", None
        for _ in range(MAX_RETRIES):
            try:
                limiter.acquire()
                raw = call_with_backoff(lambda: call_llm(client, deployment, messages, max_tokens=MAX_TOKENS)) or ""
                parsed = parse_response(raw, multilabel)
            except Exception as e:
                raw = f"<LLM call failed: {type(e).__name__}: {e}>"
                parsed = None
            if parsed is not None:
                break
        entry = dump_entry(sample, parsed, raw, list(sample.labels))
        with lock:
            results_by_id[sample.id] = entry
            state["results"] = list(results_by_id.values())
            completed_count[0] += 1
            if completed_count[0] % FLUSH_EVERY == 0:
                _flush(path, state)
        if progress_cb is not None:
            progress_cb()

    def _run_all(progress_cb: Callable[[], None] | None) -> None:
        with ThreadPoolExecutor(max_workers=concurrency) as executor:
            futs = [executor.submit(_process, s, progress_cb) for s in pending]
            for fut in as_completed(futs):
                fut.result()

    desc = f"  {dataset_key} / {model_key} / {technique} / {language}"
    if on_progress is not None:
        _run_all(on_progress)
    else:
        with Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}"),
            BarColumn(),
            MofNCompleteColumn(),
            TimeElapsedColumn(),
        ) as progress:
            task = progress.add_task(desc, total=len(pending))
            _run_all(lambda: progress.advance(task))

    state["results"] = list(results_by_id.values())
    state["metadata"]["completed_at"] = _now_iso()
    _flush(path, state)
    successes = sum(1 for e in state["results"] if e["success"] == 1)
    print(f"[done] {successes}/{len(state['results'])} success -> {path}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="phase1_nli_eval.nli_pipeline",
        description="Phase 1 NLI evaluation: dataset x model x technique x language.",
    )
    p.add_argument("-d", "--data", required=True, choices=sorted(DATASETS),
                   help="Dataset key.")
    p.add_argument("-m", "--model", required=True, choices=sorted(MODELS),
                   help="Model key from clients.models.MODELS.")
    p.add_argument("-t", "--technique", required=True, choices=TECHNIQUES,
                   help="Prompting technique.")
    p.add_argument("-l", "--language", required=True, choices=list(LANGUAGES),
                   help="Prompt-body language (independent of dataset language).")
    p.add_argument("--resume", action="store_true",
                   help="Resume an existing results file for this combination.")
    p.add_argument("--limit", type=int, default=None, metavar="N",
                   help="Process at most N samples.")
    return p


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    return run(args.data, args.model, args.technique, args.language, args.resume, args.limit)


if __name__ == "__main__":
    raise SystemExit(main())
