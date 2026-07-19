"""LLM-as-judge runner: discover Phase-1 result files and judge scorable
entries, with resume, concurrency, and incremental flush.

Run: python -m phase1_nli_eval.eval_runner --data fracas --model gpt-4o [--technique zero-shot] [--resume] [--limit N]
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
from phase1_nli_eval.concurrency import MAX_CONCURRENCY, RPM_PER_DEPLOYMENT, call_with_backoff, get_limiter
from phase1_nli_eval.eval_judge import build_judge_prompt, build_score_object, is_scorable, parse_judge_response
from phase1_nli_eval.nli_pipeline import DATASETS, RESULTS_DIR, TECHNIQUES

load_dotenv()

SCORES_DIR = RESULTS_DIR.parent / "judge_scores"  # sibling to results/, mirrors its {dataset}/ layout
FLUSH_EVERY = 10
MAX_TOKENS = 500
MAX_RETRIES = 3
LANGUAGE = "en"  # el is never judged, per team decision


def _now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _new_state(judge_model: str, result_path: Path, phase1_metadata: dict) -> dict:
    return {
        "metadata": {
            "judge_model": judge_model,
            "source_file": result_path.name,
            "dataset": phase1_metadata.get("dataset"),
            "model": phase1_metadata.get("model"),
            "technique": phase1_metadata.get("technique"),
            "language": phase1_metadata.get("language"),
            "started_at": _now_iso(),
            "completed_at": None,
            "skipped_count": 0,
            "judge_failed_count": 0,
        },
        "scores": [],
    }


def _flush(path: Path, state: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")


def judge_file(
    result_path: Path,
    judge_model: str,
    resume: bool,
    limit: int | None = None,
    on_progress: Callable[[], None] | None = None,
    concurrency: int = MAX_CONCURRENCY,
    rpm: int = RPM_PER_DEPLOYMENT,
) -> Path:
    provider = MODELS[judge_model]["provider"]
    assert_env(provider)
    client = get_client(judge_model)
    deployment = MODELS[judge_model]["deployment"]

    data = json.loads(result_path.read_text(encoding="utf-8"))
    phase1_metadata, entries = data.get("metadata", {}), data.get("results", [])

    scores_path = SCORES_DIR / result_path.parent.name / f"{result_path.stem}__scores.json"
    if resume and scores_path.exists():
        state = json.loads(scores_path.read_text(encoding="utf-8"))
        scores_by_id = {s["id"]: s for s in state["scores"]}
    else:
        state = _new_state(judge_model, result_path, phase1_metadata)
        scores_by_id = {}

    scorable = [e for e in entries if is_scorable(e)]
    skipped_count = len(entries) - len(scorable)
    pending = [e for e in scorable if e["id"] not in scores_by_id]
    if limit is not None:
        pending = pending[:limit]

    limiter = get_limiter(deployment, rpm)
    lock = threading.Lock()
    judge_failed = [0]
    done_count = [0]

    def _process(entry: dict, progress_cb: Callable[[], None] | None) -> None:
        messages = build_judge_prompt(entry)
        parsed = None
        for _ in range(MAX_RETRIES):
            try:
                limiter.acquire()
                raw = call_with_backoff(lambda: call_llm(client, deployment, messages, max_tokens=MAX_TOKENS)) or ""
                parsed = parse_judge_response(raw)
            except Exception:
                parsed = None
            if parsed is not None:
                break
        with lock:
            if parsed is not None:
                scores_by_id[entry["id"]] = build_score_object(entry, parsed)
            else:
                judge_failed[0] += 1
            state["scores"] = list(scores_by_id.values())
            done_count[0] += 1
            if done_count[0] % FLUSH_EVERY == 0:
                _flush(scores_path, state)
        if progress_cb is not None:
            progress_cb()

    def _run_all(progress_cb: Callable[[], None] | None) -> None:
        with ThreadPoolExecutor(max_workers=concurrency) as executor:
            futs = [executor.submit(_process, e, progress_cb) for e in pending]
            for fut in as_completed(futs):
                fut.result()

    desc = f"  {result_path.stem}"
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

    state["scores"] = list(scores_by_id.values())
    state["metadata"]["skipped_count"] = skipped_count
    state["metadata"]["judge_failed_count"] = judge_failed[0]
    state["metadata"]["completed_at"] = _now_iso()
    _flush(scores_path, state)
    print(f"[done] {len(state['scores'])} scored, {judge_failed[0]} judge-failed -> {scores_path}")
    return scores_path


def run(judge_model: str, dataset_key: str, technique: str, resume: bool, limit: int | None = None) -> int:
    pattern = f"{dataset_key}__*__{technique}__{LANGUAGE}.json"
    result_files = sorted((RESULTS_DIR / dataset_key).glob(pattern))
    if not result_files:
        print(f"[run] no en/{technique} result files found for dataset={dataset_key}")
        return 1
    print(
        f"[run] judge_model={judge_model} dataset={dataset_key} technique={technique} "
        f"language={LANGUAGE} files={len(result_files)}"
    )
    for result_path in result_files:
        judge_file(result_path, judge_model, resume, limit)
    return 0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="phase1_nli_eval.eval_runner",
        description="LLM-as-judge scoring of Phase-1 explanations.",
    )
    p.add_argument("-m", "--model", default="gpt-4o", choices=sorted(MODELS),
                   help="Judge model key from clients.models.MODELS.")
    p.add_argument("-d", "--data", required=True, choices=sorted(DATASETS),
                   help="Dataset key whose Phase-1 result files to judge.")
    p.add_argument("-t", "--technique", default="zero-shot", choices=TECHNIQUES,
                   help="Phase-1 technique to judge. Defaults to zero-shot.")
    p.add_argument("-l", "--language", default="en", choices=["en"],
                   help="Prompt language to judge (en only).")
    p.add_argument("--resume", action="store_true",
                   help="Resume existing score files, skipping already-scored ids.")
    p.add_argument("--limit", type=int, default=None, metavar="N",
                   help="Judge at most N scorable samples per file.")
    return p


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    return run(args.model, args.data, args.technique, args.resume, args.limit)


if __name__ == "__main__":
    raise SystemExit(main())
