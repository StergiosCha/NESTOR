"""Phase 1 NLI evaluation pipeline.

Single CLI entry point. Loads one of the 5 datasets via data.loaders, runs an
LLM under a chosen prompting technique and prompt language, and writes a
per-combination JSON results file.

Phase 1 of the plan: scaffolding only. CLI parses and dispatches; the run loop
is wired in Phase 4.
"""

from __future__ import annotations

import argparse
from pathlib import Path

from data.loaders import (
    load_extended_fracas,
    load_fracas,
    load_multilabel_fracas,
    load_oyxoy,
    load_translated_fracas,
)
from data.schema import LANGUAGES, Sample
from utils.models import MODELS

DATA_DIR = Path(__file__).resolve().parent.parent / "data"

DATASETS = {
    "fracas": (load_fracas, DATA_DIR / "fracas" / "fracas.xml"),
    "fracas-translated": (
        load_translated_fracas,
        DATA_DIR / "translated_fracas" / "fracas_greek_final_ipa_team_crete.xml",
    ),
    "fracas-extended": (
        load_extended_fracas,
        DATA_DIR / "extended_fracas" / "fracas_greek_extended_team_crete.xml",
    ),
    "multilabel-fracas": (
        load_multilabel_fracas,
        DATA_DIR / "multilabel_fracas" / "multilabel_fracas.json",
    ),
    "oyxoy": (load_oyxoy, DATA_DIR / "oyxoy" / "OYXOY.json"),
}

TECHNIQUES = ("zero-shot", "few-shot", "cot")


def load_dataset(key: str) -> list[Sample]:
    loader, path = DATASETS[key]
    return loader(path)


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="phase1_nli_eval.nli_pipeline",
        description="Phase 1 NLI evaluation: dataset x model x technique x language.",
    )
    p.add_argument("-d", "--data", required=True, choices=sorted(DATASETS),
                   help="Dataset key.")
    p.add_argument("-m", "--model", required=True, choices=sorted(MODELS),
                   help="Model key from clients/utils MODELS registry.")
    p.add_argument("-t", "--technique", required=True, choices=TECHNIQUES,
                   help="Prompting technique.")
    p.add_argument("-l", "--language", required=True, choices=list(LANGUAGES),
                   help="Prompt-body language (independent of dataset language).")
    p.add_argument("--resume", action="store_true",
                   help="Resume an existing results file for this combination.")
    return p


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    samples = load_dataset(args.data)
    print(
        f"[scaffold] data={args.data} model={args.model} technique={args.technique} "
        f"language={args.language} resume={args.resume} loaded={len(samples)} samples"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
