"""
Stratified review sampling and annotator assignment.

Helpers used by review_app.py to give each human annotator a balanced,
reproducible slice of NLI explanations to review. 

Three steps:

1. build_universe:       list every explanation to review (one per dataset,
                         model, technique, language, id). English only; 
2. draw_stratified_pool: pick a reproducible ~10% sample, spread evenly across
                         dataset x model x section cells.
3. slice_for_annotator:  hand each annotator their own share of that pool.
"""
from __future__ import annotations

import hashlib
import json
import random
import re
from pathlib import Path
from typing import Iterable

# Item identity: the tuple that uniquely names one explanation across the tree.
ItemKey = tuple[str, str, str, str, str]  # (dataset, model, technique, language, id)

UNSECTIONED = "(unsectioned)"


# --------------------------------------------------------------------------
# Item identity
# --------------------------------------------------------------------------
def item_key(record: dict) -> ItemKey:
    """Stable identity tuple for one explanation."""
    return (
        str(record.get("dataset", "")),
        str(record.get("model", "")),
        str(record.get("technique", "")),
        str(record.get("language", "")),
        str(record.get("id", "")),
    )


def item_key_str(record: dict) -> str:
    """Join the identity tuple into one stable string for hashing."""
    return "\x1f".join(item_key(record))


# --------------------------------------------------------------------------
# Universe discovery
# --------------------------------------------------------------------------
def _parse_stem(stem: str) -> tuple[str, str, str, str]:
    """`{dataset}__{model}__{technique}__{language}` → its four parts.

    Dataset/model names use single hyphens, never the `__` separator, so
    splitting on `__` is safe even for names like `fracas-extended`.
    """
    parts = stem.split("__")
    parts += [""] * (4 - len(parts))
    return parts[0], parts[1], parts[2], parts[3]


def _section_of(row: dict) -> str:
    """Derive the stratification section for one result row from fracas_sections or tags.
    If both are missing, return UNSECTIONED.
    """
    secs = row.get("fracas_sections")
    if isinstance(secs, list):
        secs = secs[0] if secs else None
    if secs:
        return str(secs)
    tags = row.get("tags")
    if isinstance(tags, list):
        tags = tags[0] if tags else None
    if tags:
        return str(tags).split(":", 1)[0]
    return UNSECTIONED


def build_universe(results_root) -> list[dict]:
    """Scan every ``*.json`` under ``results_root`` and return one
    record per eligible explanation.

    Only English zero-shot files are kept matching the LLM judge's scope.
    
    Records carry only what sampling needs:
    {dataset, model, technique, language, id, section}.
    """
    root = Path(results_root)
    universe: list[dict] = []
    if not root.exists():
        return universe
    for path in sorted(root.rglob("*.json")):
        dataset, model, technique, language = _parse_stem(path.stem)
        if language != "en" or technique != "zero-shot":
            continue
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except (json.JSONDecodeError, OSError):
            continue
        for i, row in enumerate(data.get("results", [])):
            rid = row.get("id")
            rid = f"row-{i}" if rid is None else str(rid)
            universe.append({
                "dataset": dataset,
                "model": model,
                "technique": technique,
                "language": language,
                "id": rid,
                "section": _section_of(row),
            })
    return universe


# --------------------------------------------------------------------------
# Stratified pool
# --------------------------------------------------------------------------
def _natural_key(rec: dict):
    """Sort records reproducibly; numeric id suffix ordered numerically."""
    rid = rec["id"]
    m = re.search(r"(\d+)\s*$", rid)
    id_key = (0, int(m.group(1)), rid) if m else (1, 0, rid)
    return (rec["dataset"], rec["model"], rec["technique"], rec["language"], id_key)


def draw_stratified_pool(
    universe: list[dict],
    seed: int = 42,
    fraction: float = 0.10,
    floor: int = 1,
) -> list[dict]:
    """Draw a reproducible stratified pool over ``dataset x model x section``.

    Each populated cell contributes ``max(floor, round(fraction * cell_size))``
    items (capped at the cell size). Techniques are pooled inside a cell. The
    draw is seeded and operates on naturally-sorted cells, so the same universe
    + seed always yields the same pool.
    """
    cells: dict[tuple[str, str, str], list[dict]] = {}
    for rec in universe:
        cells.setdefault((rec["dataset"], rec["model"], rec["section"]), []).append(rec)

    pool: list[dict] = []
    for cell_key in sorted(cells):
        members = sorted(cells[cell_key], key=_natural_key)
        k = min(len(members), max(floor, round(fraction * len(members))))
        rng = random.Random(f"{seed}\x1f{cell_key}")  # per-cell seed → order-independent
        pool.extend(rng.sample(members, k))
    pool.sort(key=_natural_key)
    return pool


# --------------------------------------------------------------------------
# Deterministic disjoint assignment
# --------------------------------------------------------------------------
def _score(key_str: str, username: str) -> int:
    """A fixed score for an (item, annotator) pair. Uses sha256 rather than the
    builtin ``hash`` so it is identical across processes and runs."""
    digest = hashlib.sha256(f"{key_str}\x1f{username}".encode("utf-8")).hexdigest()
    return int(digest, 16)


def owner_of(record: dict, all_usernames: Iterable[str]) -> str | None:
    """The single annotator assigned ``record`` — the one scoring highest for
    it. Same item + same annotator set always gives the same owner."""
    users = list(all_usernames)
    if not users:
        return None
    ks = item_key_str(record)
    return max(users, key=lambda u: (_score(ks, u), u))


def slice_for_annotator(
    pool: list[dict],
    username: str,
    all_usernames: Iterable[str],
    ceiling: int | None = None,
) -> list[dict]:
    """The slice of ``pool`` assigned to ``username``.

    Each item goes to whichever known username scores highest for it, so
    slices never overlap. If ``ceiling`` is set, only that annotator's
    top-``ceiling`` owned items are returned, chosen deterministically.
    """
    users = list(all_usernames)
    if username not in users:
        users.append(username)
    owned = [rec for rec in pool if owner_of(rec, users) == username]
    owned.sort(key=lambda rec: (_score(item_key_str(rec), username), item_key_str(rec)))
    if ceiling is not None and ceiling >= 0:
        owned = owned[:ceiling]
    owned.sort(key=_natural_key)
    return owned
