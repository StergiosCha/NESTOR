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
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path

import yaml
from rich import box
from rich.console import Console
from rich.table import Table
from rich.text import Text

from clients.models import MODELS
from data.schema import LANGUAGES
from phase1_nli_eval import nli_pipeline
from phase1_nli_eval.nli_pipeline import DATASETS, TECHNIQUES, run

console = Console()


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


def _print_table(rows: list[tuple[tuple[str, str, str, str], str, str, str, str, str]]) -> None:
    table = Table(box=box.ROUNDED, show_header=True, header_style="bold")
    table.add_column("dataset")
    table.add_column("model")
    table.add_column("technique")
    table.add_column("lang")
    table.add_column("status", justify="center")
    table.add_column("accuracy", justify="right")
    table.add_column("parse_fail", justify="right")
    table.add_column("llm_error", justify="right")
    table.add_column("detail")

    for combo, status, accuracy, parse_fail, llm_error, detail in rows:
        dataset, model, technique, language = combo
        status_text = Text(status, style="green bold" if status == "PASS" else "red bold")
        table.add_row(dataset, model, technique, language, status_text, accuracy, parse_fail, llm_error, detail)

    console.print()
    console.print(table)


def run_sweep(cfg: SweepConfig) -> int:
    combos = expand_combinations(cfg)
    console.print(f"[bold][sweep][/bold] {len(combos)} combination(s) to run")

    deploy_locks: dict[str, threading.Lock] = {}
    for _, model, _, _ in combos:
        dep = MODELS[model]["deployment"]
        if dep not in deploy_locks:
            deploy_locks[dep] = threading.Lock()
    n_workers = max(1, len(deploy_locks))

    rows: list[tuple[tuple[str, str, str, str], str, str, str, str, str]] = []
    rows_lock = threading.Lock()
    any_fail = [False]

    def _run_combo(enum_combo: tuple[int, tuple[str, str, str, str]]) -> None:
        i, combo = enum_combo
        _, model, _, _ = combo
        dep = MODELS[model]["deployment"]
        with deploy_locks[dep]:
            console.print(f"\n[{i}/{len(combos)}] {_combo_key(combo)}")
            try:
                run(*combo, resume=cfg.resume, limit=cfg.limit)
                summary = _read_summary(combo) or {}
                ok = summary.get("success_count", 0)
                n_total = summary.get("total", 0)
                pct = f"{100 * ok / n_total:.1f}%" if n_total else "n/a"
                accuracy = f"{ok}/{n_total} ({pct})"
                parse_fail = str(summary.get("parse_fail", "?"))
                llm_error = str(summary.get("llm_error", "?"))
                with rows_lock:
                    rows.append((combo, "PASS", accuracy, parse_fail, llm_error, ""))
            except Exception as e:
                with rows_lock:
                    any_fail[0] = True
                    rows.append((combo, "FAIL", "-", "-", "-", f"{type(e).__name__}: {e}"))
                console.print(f"  [red]FAIL:[/red] {type(e).__name__}: {e}")

    with ThreadPoolExecutor(max_workers=n_workers) as executor:
        futs = [executor.submit(_run_combo, (i, combo)) for i, combo in enumerate(combos, 1)]
        for fut in as_completed(futs):
            fut.result()

    _print_table(rows)
    return 1 if any_fail[0] else 0


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
