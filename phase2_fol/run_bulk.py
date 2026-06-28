"""Phase 2 FOL bulk runner.

Drives `fol_pipeline.run` over a Cartesian product of {dataset x model}
combinations described by a single YAML config (condition is a scalar applied to
the whole sweep). Combos sharing a model's deployment are serialised by a
per-deployment lock, so each model only ever has one run in flight; different
models run concurrently. Per-combo failures are isolated; the sweep prints a
final PASS/FAIL table sourced from each result JSON's summary block.
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
from rich.progress import BarColumn, MofNCompleteColumn, Progress, SpinnerColumn, TextColumn, TimeElapsedColumn
from rich.table import Table
from rich.text import Text

from clients.models import MODELS
from phase2_fol import fol_pipeline
from phase2_fol.fol_pipeline import DATASETS, run

console = Console()

CONDITIONS = ("c1", "c2", "c3", "c4")


@dataclass(frozen=True)
class SweepConfig:
    datasets: list[str]
    models: list[str]
    condition: str = "c1"
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
    for field, allowed in (("datasets", DATASETS), ("models", set(MODELS))):
        errs, values = _validate_list(field, raw.get(field), allowed)
        errors.extend(errs)
        parsed[field] = values

    condition = raw.get("condition", "c1")
    if condition not in CONDITIONS:
        errors.append(f"condition: unknown value {condition!r} (allowed: {list(CONDITIONS)})")
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
        condition=condition,
        resume=resume,
        limit=limit,
    )


def expand_combinations(cfg: SweepConfig) -> list[tuple[str, str]]:
    return list(itertools.product(cfg.datasets, cfg.models))


def _combo_key(combo: tuple[str, str], condition: str) -> str:
    return "__".join((*combo, condition))


def _read_summary(combo: tuple[str, str], condition: str) -> dict | None:
    path = fol_pipeline._results_path(*combo, condition)
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8")).get("summary")
    except Exception:
        return None


def _print_table(rows: list[tuple[tuple[str, str], str, str, str, str, str]]) -> None:
    table = Table(box=box.ROUNDED, show_header=True, header_style="bold")
    table.add_column("dataset")
    table.add_column("model")
    table.add_column("status", justify="center")
    table.add_column("accuracy", justify="right")
    table.add_column("unknown", justify="right")
    table.add_column("llm_error", justify="right")
    table.add_column("detail")

    for combo, status, accuracy, unknown, llm_error, detail in rows:
        dataset, model = combo
        status_text = Text(status, style="green bold" if status == "PASS" else "red bold")
        table.add_row(dataset, model, status_text, accuracy, unknown, llm_error, detail)

    console.print()
    console.print(table)


def run_sweep(cfg: SweepConfig) -> int:
    combos = expand_combinations(cfg)
    console.print(
        f"[bold][sweep][/bold] {len(combos)} combination(s) to run (condition={cfg.condition})"
    )

    deploy_locks: dict[str, threading.Lock] = {}
    for _, model in combos:
        dep = MODELS[model]["deployment"]
        deploy_locks.setdefault(dep, threading.Lock())
    n_workers = max(1, len(deploy_locks))

    rows: list[tuple[tuple[str, str], str, str, str, str, str]] = []
    rows_lock = threading.Lock()
    any_fail = [False]

    with Progress(
        SpinnerColumn(),
        TextColumn("[progress.description]{task.description}"),
        BarColumn(),
        MofNCompleteColumn(),
        TimeElapsedColumn(),
        console=console,
    ) as progress:
        sweep_task = progress.add_task("[bold]sweep[/bold]", total=len(combos))

        def _run_combo(combo: tuple[str, str]) -> None:
            dataset, model = combo
            dep = MODELS[model]["deployment"]
            combo_task = progress.add_task(f"  {_combo_key(combo, cfg.condition)}", total=None)

            with deploy_locks[dep]:
                try:
                    run(dataset, model, cfg.condition, resume=cfg.resume, limit=cfg.limit,
                        on_progress=lambda: progress.advance(combo_task))
                    summary = _read_summary(combo, cfg.condition) or {}
                    ok = summary.get("success_count", 0)
                    n_total = summary.get("total", 0)
                    pct = f"{100 * ok / n_total:.1f}%" if n_total else "n/a"
                    accuracy = f"{ok}/{n_total} ({pct})"
                    unknown = str(summary.get("unknown", "?"))
                    llm_error = str(summary.get("llm_error", "?"))
                    detail = f"proved={summary.get('proved', 0)}, countermodel={summary.get('countermodel', 0)}"
                    with rows_lock:
                        rows.append((combo, "PASS", accuracy, unknown, llm_error, detail))
                except Exception as e:
                    with rows_lock:
                        any_fail[0] = True
                        rows.append((combo, "FAIL", "-", "-", "-", f"{type(e).__name__}: {e}"))
                    console.print(f"  [red]FAIL:[/red] {_combo_key(combo, cfg.condition)}: {type(e).__name__}: {e}")
                finally:
                    progress.update(combo_task, visible=False)
                    progress.advance(sweep_task)

        with ThreadPoolExecutor(max_workers=n_workers) as executor:
            futs = [executor.submit(_run_combo, combo) for combo in combos]
            for fut in as_completed(futs):
                fut.result()

    _print_table(rows)
    return 1 if any_fail[0] else 0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        prog="phase2_fol.run_bulk",
        description="Phase 2 FOL bulk runner: sweep dataset x model from a YAML config.",
    )
    p.add_argument("--config", required=True, type=Path, help="Path to YAML sweep config.")
    args = p.parse_args(argv)
    cfg = load_sweep_config(args.config)
    return run_sweep(cfg)


if __name__ == "__main__":
    raise SystemExit(main())
