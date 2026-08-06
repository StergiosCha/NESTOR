"""Shared helpers for the NESTOR analysis scripts.

Everything the analysis layer needs to reconcile the four data sources:

  phase1_nli_eval/results/     180 files: {dataset}__{model}__{technique}__{language}.json
  phase1_nli_eval/judge_scores/ 39 files: ...__scores.json  (zero-shot / en only)
  phase2_fol/results/           46 files: {dataset}__{model}__c1.json
  reviews/                      20 files: {stem}.{reviewer}.reviews.json

The awkward parts this module hides:

* Gold labels are always lists; predictions are a bare string for
  fracas / fracas-translated / fracas-extended but a list for
  fracas-multilabel / oyxoy. `label_set()` normalises both.
* Label vocabularies differ (FraCaS yes/no/unknown/undef vs
  Entailment/Contradiction/Unknown). `norm_label()` maps to one vocabulary.
* Sections are carried in `fracas_sections` for four datasets but are
  absent for fracas-extended, and can be re-derived from the FraCaS
  problem number for fracas / fracas-translated.
* Item ids are zero-padded (`fracas-0001`) in Phase 1/judge/FOL but bare
  (`fracas-1`) in the Coq pipeline's loader. `item_number()` bridges them.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
PHASE1_RESULTS = REPO / "phase1_nli_eval" / "results"
JUDGE_SCORES = REPO / "phase1_nli_eval" / "judge_scores"
FOL_RESULTS = REPO / "phase2_fol" / "results"
COQ_RESULTS = REPO / "phase2_coq" / "results"
REVIEWS = REPO / "reviews"

ANALYSIS = REPO / "analysis"
OUT_TABLES = ANALYSIS / "tables"
OUT_FIGS = ANALYSIS / "figs"

DATASETS = [
    "fracas",
    "fracas-translated",
    "fracas-extended",
    "fracas-multilabel",
    "oyxoy",
]

DATASET_SIZES = {
    "fracas": 342,
    "fracas-translated": 342,
    "fracas-extended": 427,
    "fracas-multilabel": 713,
    "oyxoy": 1049,
}

DATASET_DISPLAY = {
    "fracas": "FraCaS",
    "fracas-translated": "FraCaS-EL",
    "fracas-extended": "FraCaS-Ext",
    "fracas-multilabel": "FraCaS-ML",
    "oyxoy": "OYXOY",
}

MODELS = [
    "gpt-4o",
    "gpt-5.4",
    "deepseek-r1",
    "deepseek-v4-pro",
    "grok-4-20",
    "grok-4-20-reasoning",
    "llama-3.3-70b",
    "llama-4-maverick",
    "mistral-large-3",
]

TECHNIQUES = ["zero-shot", "few-shot"]
LANGUAGES = ["en", "el"]

LABELS = ["Entailment", "Contradiction", "Unknown"]

# ------------------------------------------------------------------
# Label normalisation
# ------------------------------------------------------------------

_LABEL_MAP = {
    "yes": "Entailment",
    "entailment": "Entailment",
    "entail": "Entailment",
    "entails": "Entailment",
    "e": "Entailment",
    "no": "Contradiction",
    "contradiction": "Contradiction",
    "contradict": "Contradiction",
    "contradicts": "Contradiction",
    "contradictory": "Contradiction",
    "c": "Contradiction",
    "unknown": "Unknown",
    "undef": "Unknown",
    "undecided": "Unknown",
    "neutral": "Unknown",
    "unk": "Unknown",
    "n": "Unknown",
}


def norm_label(value):
    """Map any label spelling onto Entailment/Contradiction/Unknown.

    Returns None for missing or unmappable values so callers can count
    them as failures rather than silently folding them into a class.
    """
    if value is None:
        return None
    s = str(value).strip().lower()
    if not s:
        return None
    return _LABEL_MAP.get(s)


def label_set(value):
    """Normalise a gold or predicted value to a frozenset of canonical labels."""
    if value is None:
        return frozenset()
    items = value if isinstance(value, (list, tuple, set, frozenset)) else [value]
    return frozenset(x for x in (norm_label(v) for v in items) if x)


def correctness(pred, gold):
    """Return (strict, partial) correctness, or (None, None) if no prediction.

    strict  -- predicted label set equals gold label set
    partial -- predicted set is a subset of the gold set

    Both rules were checked against the stored summary fields of all 180
    Phase 1 result files:

    * strict reproduces `summary.success_count` in 180/180 files.
    * 116 files also carry `summary.partial_success_count`. The subset
      rule reproduces it in 112; an overlap rule (any shared label)
      reproduces it in only 44. Overlap over-credits a prediction of
      {Entailment, Unknown} against gold {Unknown}, which the runner
      counts as wrong.
    * The 4 exceptions are the mistral-large-3 x fracas files, which
      store `partial_success_count: 0` alongside a non-zero
      `success_count` (214/208/241/232). FraCaS is single-label, so
      partial cannot be below strict; that stored 0 is a defect in those
      four files, not evidence against the subset rule. The audit script
      reports them.

    For the three single-label datasets the two measures coincide.
    """
    p, g = label_set(pred), label_set(gold)
    if not p:
        return None, None
    return (p == g), (p <= g)


def primary(value):
    """Single representative label, for confusion matrices. None if ambiguous."""
    s = label_set(value)
    return next(iter(s)) if len(s) == 1 else None


# ------------------------------------------------------------------
# FraCaS sections
# ------------------------------------------------------------------

SECTION_NUM = {
    "Generalized Quantifiers": 1,
    "Plurals": 2,
    "Anaphora": 3,
    "Ellipsis": 4,
    "Adjectives": 5,
    "Comparatives": 6,
    "Temporal Reference": 7,
    "Verbs": 8,
    "Attitudes": 9,
}
SECTION_NAME = {v: k for k, v in SECTION_NUM.items()}
SECTION_SHORT = {
    1: "1 Quant",
    2: "2 Plural",
    3: "3 Anaph",
    4: "4 Ellip",
    5: "5 Adj",
    6: "6 Comp",
    7: "7 Temp",
    8: "8 Verbs",
    9: "9 Attit",
}

# Same boundaries as utils/fracas.py, kept here so the analysis layer has
# no import dependency on the pipeline package.
FRACAS_BOUNDARIES = [
    (1, 80, 1), (81, 113, 2), (114, 141, 3), (142, 196, 4),
    (197, 219, 5), (220, 250, 6), (251, 325, 7), (326, 333, 8),
    (334, 346, 9),
]


def item_number(item_id):
    """Trailing integer of an item id: 'fracas-0001' -> 1, 'fracas-1' -> 1."""
    m = re.search(r"(\d+)\s*$", str(item_id))
    return int(m.group(1)) if m else None


def fracas_section_from_number(n):
    """FraCaS problem number -> section number, or None if out of range."""
    if n is None:
        return None
    for low, high, sec in FRACAS_BOUNDARIES:
        if low <= n <= high:
            return sec
    return None


def sections_of(item, dataset=None):
    """Section numbers for an item.

    Prefers the `fracas_sections` field written by the Phase 1/FOL
    runners; falls back to the FraCaS problem-number boundaries for the
    two datasets that share FraCaS numbering. Returns [] when the
    dataset carries no section information (fracas-extended).
    """
    names = item.get("fracas_sections") or []
    nums = [SECTION_NUM[n] for n in names if n in SECTION_NUM]
    if nums:
        return sorted(set(nums))
    if dataset in ("fracas", "fracas-translated"):
        sec = fracas_section_from_number(item_number(item.get("id")))
        return [sec] if sec else []
    return []


# ------------------------------------------------------------------
# File discovery
# ------------------------------------------------------------------

def load_json(path):
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def parse_phase1_name(path):
    """'fracas__gpt-4o__zero-shot__en.json' -> dict, or None if off-pattern."""
    stem = Path(path).name
    if not stem.endswith(".json"):
        return None
    parts = stem[:-5].split("__")
    if len(parts) != 4:
        return None
    dataset, model, technique, language = parts
    return {
        "dataset": dataset,
        "model": model,
        "technique": technique,
        "language": language,
        "path": Path(path),
    }


def phase1_files(dataset=None, model=None, technique=None, language=None):
    """Well-formed Phase 1 result files, sorted.

    Only files under results/{dataset}/ with the 4-part name are returned;
    the loose legacy files at the results root are ignored (and reported
    by the audit script).
    """
    out = []
    for p in sorted(PHASE1_RESULTS.glob("*/*.json")):
        info = parse_phase1_name(p)
        if not info:
            continue
        if dataset and info["dataset"] != dataset:
            continue
        if model and info["model"] != model:
            continue
        if technique and info["technique"] != technique:
            continue
        if language and info["language"] != language:
            continue
        out.append(info)
    return out


def iter_phase1(**kw):
    """Yield (info, metadata, items) for each matching Phase 1 file."""
    for info in phase1_files(**kw):
        d = load_json(info["path"])
        yield info, d.get("metadata", {}), d.get("results", [])


def parse_judge_name(path):
    """'fracas__gpt-4o__zero-shot__en__scores.json' -> dict."""
    stem = Path(path).name
    if not stem.endswith("__scores.json"):
        return None
    parts = stem[: -len("__scores.json")].split("__")
    if len(parts) != 4:
        return None
    dataset, model, technique, language = parts
    return {
        "dataset": dataset,
        "model": model,
        "technique": technique,
        "language": language,
        "path": Path(path),
    }


# Judge scores exist for a tenth model, gpt-5.4-pro, whose Phase 1 source
# files are absent from the repository (verified: the three
# *__gpt-5.4-pro__* score files name a source_file that does not exist).
# Those 1,708 scored items cannot be joined to a prediction, so every
# accessor below restricts itself to the nine designed models.
KNOWN_MODELS_ONLY = True


def judge_files(dataset=None, model=None, include_orphans=False):
    """Judge score files, restricted to the nine designed models.

    Judge scores also exist for a tenth model, gpt-5.4-pro (three files:
    fracas, fracas-translated, oyxoy; 1,708 scored items). Their
    `metadata.source_file` names a Phase 1 result file that is NOT
    present in the repository, so those scores cannot be joined to a
    prediction and the model has no accuracy anywhere else in the study.
    They are excluded by default; pass include_orphans=True to inspect
    them. The audit script reports them as a defect.
    """
    out = []
    for p in sorted(JUDGE_SCORES.glob("*/*.json")):
        info = parse_judge_name(p)
        if not info:
            continue
        if dataset and info["dataset"] != dataset:
            continue
        if model and info["model"] != model:
            continue
        if not include_orphans and info["model"] not in MODELS:
            continue
        out.append(info)
    return out


def iter_judge(**kw):
    """Yield (info, metadata, scores) for each judge score file."""
    for info in judge_files(**kw):
        d = load_json(info["path"])
        yield info, d.get("metadata", {}), d.get("scores", [])


def parse_fol_name(path):
    """'fracas__gpt-4o__c1.json' -> dict."""
    stem = Path(path).name
    if not stem.endswith(".json"):
        return None
    parts = stem[:-5].split("__")
    if len(parts) != 3:
        return None
    dataset, model, condition = parts
    return {
        "dataset": dataset,
        "model": model,
        "condition": condition,
        "path": Path(path),
    }


FOL_MIN_COMPLETE = 0.95


def fol_files(dataset=None, model=None, condition=None, include_partial=False):
    """FOL result files, excluding cells that did not run to completion.

    A cell still in flight (or killed early) reports accuracy over the
    handful of items it managed, so pooling it with complete cells weights
    e.g. 30 items as heavily as oyxoy's 1,049 and silently shifts every
    aggregate. Only cells with at least FOL_MIN_COMPLETE of their dataset's
    item count are returned; `include_partial=True` returns them anyway and
    `partial_fol_files()` lists what was skipped so a caller can report it.
    """
    out = []
    for p in sorted(FOL_RESULTS.glob("*/*.json")):
        info = parse_fol_name(p)
        if not info:
            continue
        if dataset and info["dataset"] != dataset:
            continue
        if model and info["model"] != model:
            continue
        if condition and info["condition"] != condition:
            continue
        if not include_partial:
            target = DATASET_SIZES.get(info["dataset"])
            n = len(load_json(info["path"]).get("results", []))
            if target and n < FOL_MIN_COMPLETE * target:
                continue
        out.append(info)
    return out


def partial_fol_files():
    """FOL cells excluded by fol_files() for being incomplete."""
    complete = {i["path"] for i in fol_files()}
    skipped = []
    for info in fol_files(include_partial=True):
        if info["path"] in complete:
            continue
        target = DATASET_SIZES.get(info["dataset"]) or 0
        n = len(load_json(info["path"]).get("results", []))
        skipped.append({**info, "n_items": n, "expected": target})
    return skipped


def iter_fol(**kw):
    """Yield (info, metadata, results) for each FOL result file."""
    for info in fol_files(**kw):
        d = load_json(info["path"])
        yield info, d.get("metadata", {}), d.get("results", [])


def parse_review_name(path):
    """'fracas__deepseek-r1__zero-shot__en.penny_kyriazi.reviews.json' -> dict."""
    name = Path(path).name
    if not name.endswith(".reviews.json"):
        return None
    base = name[: -len(".reviews.json")]
    if "." not in base:
        return None
    stem, reviewer = base.rsplit(".", 1)
    parts = stem.split("__")
    if len(parts) != 4:
        return None
    dataset, model, technique, language = parts
    return {
        "dataset": dataset,
        "model": model,
        "technique": technique,
        "language": language,
        "reviewer": reviewer,
        "path": Path(path),
    }


def review_files():
    out = []
    for p in sorted(REVIEWS.glob("*.reviews.json")):
        info = parse_review_name(p)
        if info:
            out.append(info)
    return out


def iter_reviews():
    """Yield (info, {item_id: review_dict}) for each human review file."""
    for info in review_files():
        yield info, load_json(info["path"])


COQ_MIN_COMPLETE = 0.9


def coq_files(include_partial=False):
    """Coq result files from the fixed pipeline.

    The krikri pilot files are excluded: they predate the pipeline fixes
    and were produced with the inoperative T2/T3 section mapping, so
    their rates are not comparable to post-fix runs.

    Cells that stopped early are also excluded by default. A cell holding
    7 of 27 items reports a real rate over those 7, but averaging it with
    complete cells weights 7 items as heavily as 27 and silently shifts
    every aggregate. `include_partial=True` returns them anyway, and
    `partial_coq_files()` lists what was skipped so a caller can report it
    rather than lose it.

    Completeness is judged per (dataset, tier, condition). The DATASET
    must be part of the key: the five corpora have different sizes (342 to
    1049 items), so grouping only by (tier, condition) makes the target the
    largest dataset in the group and silently drops every cell from a
    smaller corpus. That failure mode is invisible in the output and
    confounds the tier contrast with dataset -- with all five datasets at
    T0 but only fracas at T1/T2, it left T0=oyxoy vs T1/T2=fracas.

    Within a group the target is the intended dataset size where known,
    falling back to the largest observed count (the intended n varies with
    --stratified / --limit and is not recorded per file).
    """
    cands = [p for p in sorted(COQ_RESULTS.glob("**/*.json"))
             if not p.name.startswith(("krikri", "harness_validation"))]
    if include_partial:
        return cands

    counts, groups = {}, {}
    for p in cands:
        try:
            meta, items = read_coq_file(p)
        except Exception:
            continue
        counts[p] = len(items)
        key = (meta.get("dataset"), meta.get("prompt_tier"),
               meta.get("condition"))
        groups.setdefault(key, []).append(p)

    keep = []
    for key, paths in groups.items():
        dataset = key[0]
        target = DATASET_SIZES.get(dataset) or max(counts[p] for p in paths)
        for p in paths:
            if target and counts[p] >= COQ_MIN_COMPLETE * target:
                keep.append(p)
    return sorted(keep)


def partial_coq_files():
    """[(path, n_items, n_expected), ...] for cells excluded as incomplete."""
    complete = set(coq_files())
    out = []
    all_files = coq_files(include_partial=True)
    counts, groups = {}, {}
    for p in all_files:
        try:
            meta, items = read_coq_file(p)
        except Exception:
            continue
        counts[p] = len(items)
        groups.setdefault((meta.get("prompt_tier"), meta.get("condition")),
                          []).append(p)
    for key, paths in groups.items():
        target = max(counts[p] for p in paths)
        for p in paths:
            if p not in complete:
                out.append((p, counts[p], target))
    return sorted(out)


def read_coq_file(path):
    """Return (metadata, results) for either Coq output schema."""
    d = load_json(path)
    if isinstance(d, list):
        return {}, d
    return d.get("metadata", {}), d.get("results", d.get("items", []))


# ------------------------------------------------------------------
# Output helpers
# ------------------------------------------------------------------

def ensure_dirs():
    OUT_TABLES.mkdir(parents=True, exist_ok=True)
    OUT_FIGS.mkdir(parents=True, exist_ok=True)


def save_table(df, name, index=False):
    """Write a DataFrame to analysis/tables/<name> and echo its shape."""
    ensure_dirs()
    path = OUT_TABLES / name
    df.to_csv(path, index=index)
    print(f"  wrote {path.relative_to(REPO)}  ({df.shape[0]}x{df.shape[1]})")
    return path


def fig_path(name):
    ensure_dirs()
    return OUT_FIGS / name


def save_fig(fig, name, dpi=200):
    path = fig_path(name)
    fig.savefig(path, dpi=dpi, bbox_inches="tight")
    print(f"  wrote {path.relative_to(REPO)}")
    return path
