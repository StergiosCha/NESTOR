"""Phase 1 NLI evaluation pipeline.

Single CLI entry point. Loads one of the 5 datasets via data.loaders, runs an
LLM under a chosen prompting technique and prompt language, normalises the
response to a canonical Result, and writes a per-combination JSON results file.
"""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path

from dotenv import load_dotenv

from clients.azure import assert_env, call_llm, get_client
from data.loaders import load_dataset
from data.schema import LANGUAGES, MULTILABEL_SOURCES, Sample, dump_entry, parse_response
from phase1_nli_eval.prompts import build_prompt, select_examples
from clients.models import MODELS

load_dotenv()

RESULTS_DIR = Path(__file__).resolve().parent / "results"

DATASETS = {"fracas", "fracas-translated", "fracas-extended", "fracas-multilabel", "oyxoy"}

TECHNIQUES = ("zero-shot", "few-shot", "cot")
FLUSH_EVERY = 10
MAX_TOKENS = 800
FEW_SHOT_K = 3


def _results_path(dataset_key: str, model_key: str, technique: str, language: str) -> Path:
    return RESULTS_DIR / f"{dataset_key}__{model_key}__{technique}__{language}.json"


def _now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _new_state(dataset_key: str, model_key: str, technique: str, language: str, multilabel: bool) -> dict:
    return {
        "metadata": {
            "dataset": dataset_key,
            "model": model_key,
            "technique": technique,
            "language": language,
            "multilabel": multilabel,
            "started_at": _now_iso(),
            "completed_at": None,
        },
        "results": [],
    }


def _flush(path: Path, state: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")


def run(dataset_key: str, model_key: str, technique: str, language: str, resume: bool, limit: int | None = None) -> int:
    multilabel = dataset_key in MULTILABEL_SOURCES
    provider = MODELS[model_key]["provider"]
    assert_env(provider)
    client = get_client(model_key)
    deployment = MODELS[model_key]["deployment"]

    samples = load_dataset(dataset_key)
    path = _results_path(dataset_key, model_key, technique, language)

    if resume and path.exists():
        state = json.loads(path.read_text(encoding="utf-8"))
        completed = {e["id"] for e in state["results"]}
    else:
        state = _new_state(dataset_key, model_key, technique, language, multilabel)
        completed = set()

    pending = [s for s in samples if s.id not in completed]
    if limit is not None:
        pending = pending[:limit]
    total, skipped = len(samples), len(samples) - len(pending)
    print(
        f"[run] dataset={dataset_key} model={model_key} technique={technique} "
        f"language={language} multilabel={multilabel} total={total} skipped(resume)={skipped}"
    )

    pool = samples if technique == "few-shot" else []
    for i, sample in enumerate(pending, start=1):
        examples = select_examples(sample, pool, k=FEW_SHOT_K) if technique == "few-shot" else None
        messages = build_prompt(
            sample,
            technique,
            language,
            multilabel,
            examples=examples,
        )
        try:
            raw = call_llm(client, deployment, messages, max_tokens=MAX_TOKENS) or ""
            parsed = parse_response(raw, multilabel)
        except Exception as e:
            raw = f"<LLM call failed: {type(e).__name__}: {e}>"
            parsed = None
        state["results"].append(dump_entry(sample, parsed, raw, list(sample.labels)))
        if i % FLUSH_EVERY == 0:
            _flush(path, state)
            print(f"  [{i}/{len(pending)}] flushed -> {path.name}")

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
