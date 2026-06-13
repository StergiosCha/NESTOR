"""Build the Phase 1 master table from the per-combination result JSONs.

Discovers every ``<dataset>/<dataset>__<model>__<technique>__<language>.json``
result file, normalises each stored item into one long-format row, and persists
the table as Parquet (canonical) plus a CSV companion. One row per
``item x combination``; every result JSON is read strictly read-only.

``status`` mirrors ``nli_pipeline.summarize_results`` exactly; ``LABELS`` and the
results location are reused from ``data.schema`` / ``nli_pipeline``, never
re-defined here.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Iterable, cast

import pandas as pd

from phase1_nli_eval.nli_pipeline import RESULTS_DIR

LLM_ERROR_PREFIX = "<LLM call failed"

DEFAULT_MASTER_PATH = Path(__file__).resolve().parent / "master.parquet"
DEFAULT_MASTER_CSV = DEFAULT_MASTER_PATH.with_suffix(".csv")

MASTER_COLUMNS = [
    "dataset", "model", "technique", "language", "crosslingual", "multilabel_source",
    "id", "source", "sample_language", "premise", "hypothesis",
    "tags", "fracas_sections",
    "gold", "predicted", "multilabel_sample",
    "success", "partial_success", "status",
]


def load_result_files(results_dir: Path = RESULTS_DIR) -> list[dict]:
    """Read every per-combination result file under ``results_dir`` (read-only)."""
    paths = sorted(p for p in results_dir.glob("*/*.json") if "__" in p.name)
    return [json.loads(p.read_text(encoding="utf-8")) for p in paths]


def _as_labels(value: object) -> list[str] | None:
    """Normalise a stored label payload to a list, or ``None`` when absent.

    ``predicted`` is a string (single-label), a list (multilabel), or ``None``
    (parse/LLM failure). Wrapping a lone string gives every row one column type
    so it round-trips through Parquet and CSV; ``None`` stays distinct.
    """
    if value is None:
        return None
    if isinstance(value, str):
        return [value]
    return list(cast(Iterable[str], value))


def resolve_status(entry: dict) -> str:
    """Per-row status: ok / parse_fail / llm_error."""
    raw = entry.get("raw")
    if isinstance(raw, str) and raw.startswith(LLM_ERROR_PREFIX):
        return "llm_error"
    if entry.get("predicted") is None:
        return "parse_fail"
    return "ok"


def build_row(meta: dict, entry: dict) -> dict:
    """Build one master-table row from a combo's metadata and one result entry."""
    gold = list(entry.get("gold", []))
    return {
        "dataset": meta.get("dataset"),
        "model": meta.get("model"),
        "technique": meta.get("technique"),
        "language": meta.get("language"),
        "crosslingual": meta.get("crosslingual"),
        "multilabel_source": meta.get("multilabel"),
        "id": entry.get("id"),
        "source": entry.get("source"),
        "sample_language": entry.get("language"),
        "premise": entry.get("premise"),
        "hypothesis": entry.get("hypothesis"),
        "tags": list(entry.get("tags", [])),
        "fracas_sections": list(entry.get("fracas_sections", [])),
        "gold": gold,
        "predicted": _as_labels(entry.get("predicted")),
        "multilabel_sample": len(gold) > 1,
        "success": int(entry.get("success", 0)),
        "partial_success": int(entry.get("partial_success", entry.get("success", 0))),
        "status": resolve_status(entry),
    }


def build_master(results_dir: Path = RESULTS_DIR) -> pd.DataFrame:
    """Load every result file into one master table, one row per item x combination."""
    rows = [build_row(data["metadata"], entry)
            for data in load_result_files(results_dir)
            for entry in data["results"]]
    return pd.DataFrame(rows, columns=MASTER_COLUMNS)


def save_master(df: pd.DataFrame, path: Path = DEFAULT_MASTER_PATH) -> Path:
    """Write the master table to Parquet."""
    path = Path(path)
    df.to_parquet(path, index=False)
    return path


def save_master_csv(df: pd.DataFrame, path: Path = DEFAULT_MASTER_CSV) -> Path:
    """Write the master table to CSV as a human-readable companion."""
    path = Path(path)
    df.to_csv(path, index=False)
    return path


def load_master(path: Path = DEFAULT_MASTER_PATH) -> pd.DataFrame:
    """Read the master table back from Parquet, preserving list columns."""
    return pd.read_parquet(path)
