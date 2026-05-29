"""Phase 1 bulk runner.

Drives `nli_pipeline.run` over a Cartesian product of
{dataset x model x technique x language} combinations described by a single
YAML config. Per-combo failures are isolated; the sweep prints a final
PASS/FAIL table sourced from each result JSON's summary block.
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
from dataclasses import dataclass
from pathlib import Path

import yaml

from clients.models import MODELS
from data.schema import LANGUAGES
from phase1_nli_eval import nli_pipeline
from phase1_nli_eval.nli_pipeline import DATASETS, TECHNIQUES, run


@dataclass(frozen=True)
class SweepConfig:
    datasets: list[str]
    models: list[str]
    techniques: list[str]
    languages: list[str]
    resume: bool = True
    limit: int | None = None


def _validate_list(field: str, values, allowed) -> tuple[list[str], list[str]]:
    if not isinstance(values, list) or not values:
        return [f"{field}: expected non-empty list, got {values!r}"], []
    errors = [f"{field}: unknown value {v!r} (allowed: {sorted(allowed)})"
              for v in values if v not in allowed]
    return errors, list(values)


def load_sweep_config(path: Path) -> SweepConfig:
    raw = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
    if not isinstance(raw, dict):
        raise ValueError(f"{path}: top-level YAML must be a mapping")

    errors: list[str] = []
    parsed: dict[str, list[str]] = {}
    for field, allowed in (
        ("datasets", DATASETS),
        ("models", set(MODELS)),
        ("techniques", set(TECHNIQUES)),
        ("languages", set(LANGUAGES)),
    ):
        errs, values = _validate_list(field, raw.get(field), allowed)
        errors.extend(errs)
        parsed[field] = values

    resume = raw.get("resume", True)
    if not isinstance(resume, bool):
        errors.append(f"resume: expected bool, got {resume!r}")
    limit = raw.get("limit", None)
    if limit is not None and not (isinstance(limit, int) and limit > 0):
        errors.append(f"limit: expected positive int or null, got {limit!r}")

    if errors:
        raise ValueError("Invalid sweep config:\n  - " + "\n  - ".join(errors))

    return SweepConfig(
        datasets=parsed["datasets"],
        models=parsed["models"],
        techniques=parsed["techniques"],
        languages=parsed["languages"],
        resume=resume,
        limit=limit,
    )


def expand_combinations(cfg: SweepConfig) -> list[tuple[str, str, str, str]]:
    return list(itertools.product(cfg.datasets, cfg.models, cfg.techniques, cfg.languages))


def _combo_key(combo: tuple[str, str, str, str]) -> str:
    return "__".join(combo)


def _read_summary(combo: tuple[str, str, str, str]) -> dict | None:
    path = nli_pipeline._results_path(*combo)
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8")).get("summary")
    except Exception:
        return None


def _print_table(rows: list[tuple[str, str, str]]) -> None:
    width = max((len(r[0]) for r in rows), default=10)
    print()
    print(f"{'combo'.ljust(width)}  status  detail")
    print(f"{'-' * width}  ------  ------")
    for combo, status, detail in rows:
        print(f"{combo.ljust(width)}  {status:<6}  {detail}")


def run_sweep(cfg: SweepConfig) -> int:
    combos = expand_combinations(cfg)
    print(f"[sweep] {len(combos)} combination(s) to run")
    rows: list[tuple[str, str, str]] = []
    any_fail = False
    for i, combo in enumerate(combos, start=1):
        key = _combo_key(combo)
        print(f"\n[sweep {i}/{len(combos)}] {key}")
        try:
            run(*combo, resume=cfg.resume, limit=cfg.limit)
            summary = _read_summary(combo) or {}
            detail = f"{summary.get('success_count', '?')}/{summary.get('total', '?')}"
            rows.append((key, "PASS", detail))
        except Exception as e:
            any_fail = True
            rows.append((key, "FAIL", f"{type(e).__name__}: {e}"))
            print(f"  [sweep] FAIL: {type(e).__name__}: {e}")

    _print_table(rows)
    return 1 if any_fail else 0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        prog="phase1_nli_eval.run_bulk",
        description="Phase 1 bulk runner: sweep many combinations from a YAML config.",
    )
    p.add_argument("--config", required=True, type=Path,
                   help="Path to YAML sweep config.")
    args = p.parse_args(argv)
    cfg = load_sweep_config(args.config)
    return run_sweep(cfg)


if __name__ == "__main__":
    raise SystemExit(main())
