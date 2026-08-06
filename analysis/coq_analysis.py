"""Phase 2b Coq pipeline: compilation, proof and accuracy rates per tier.

Reads phase2_coq/results/ and writes tier x model tables. Designed to
degrade gracefully: with no post-fix result files it emits empty tables
with the correct columns and a placeholder note, so the paper build and
the rest of the analysis run before the 27 Azure jobs have been executed.

  tables/coq_summary.csv          per file: compilation / proof / accuracy
  tables/coq_by_tier.csv          tier means pooled over models
  tables/coq_attempts.csv         attempts distribution per tier
  tables/coq_error_taxonomy.csv   error categories from coqc output
  tables/coq_by_section.csv       rates per FraCaS section (T2's premise)
  tables/coq_by_item.csv          tidy per-item table

  figs/coq_compilation_by_tier.png
  figs/coq_error_taxonomy.png
  figs/coq_tier_comparison.png

The krikri pilot files are deliberately excluded (see common.coq_files):
they were produced before the section-mapping fix, so their T2/T3 runs
did not actually receive section-matched foundation files.

Usage:  python analysis/coq_analysis.py
"""

from __future__ import annotations

import sys
from collections import Counter
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as C

try:
    apply_figure_style()  # noqa: F821
except NameError:
    plt.rcParams.update({
        "figure.dpi": 120, "savefig.dpi": 200,
        "font.size": 8, "axes.titlesize": 8, "axes.labelsize": 8,
        "xtick.labelsize": 6, "ytick.labelsize": 6, "legend.fontsize": 7,
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.grid": True, "grid.alpha": 0.25, "grid.linewidth": 0.5,
    })

FOCAL = "#1f4e79"
TIERS = ["T0", "T1", "T2", "T3"]

ITEM_COLS = ["dataset", "model", "tier", "condition", "id", "gold",
             "predicted_label", "compiled", "proof_complete", "correct",
             "attempts", "n_errors", "error_category", "section"]

SUMMARY_COLS = ["dataset", "model", "tier", "condition", "n_items",
                "compilation_rate", "proof_rate", "accuracy",
                "accuracy_given_compiled", "mean_attempts",
                "n_compiled", "n_proved", "n_correct", "path"]

# Categories keyed to real coqc diagnostics; see phase2_coq/coqc_diagnosis.md
# for the probe transcript each pattern was taken from.
COQ_ERROR_RULES = [
    ("timeout", r"^TIMEOUT$|TIMEOUT"),
    ("coqc_missing", r"not found\. Install Coq|No such file or directory"),
    ("empty_output", r"Empty Coq code"),
    ("syntax_error", r"Syntax error|Syntax Error|illegal begin|was expected"),
    ("unbound_identifier", r"reference .* was not found|Unbound|Cannot find"),
    ("type_error", r"has type|is expected to have type|Illegal application|"
                   r"not a type|Type error|The term .* has type"),
    ("section_hypothesis", r"Hypothesis|Variable .* outside|not allowed inside"),
    ("tactic_failure", r"Unable to unify|No applicable tactic|"
                       r"cannot be applied|tactic failure|"
                       r"Attempt to save an incomplete proof|"
                       r"No such (?:hypothesis|assumption)|firstorder failed"),
    ("require_import", r"Cannot find a physical path|Unable to locate library"),
    ("unterminated_proof", r"There are pending proofs|Unterminated"),
]


def classify_coq_error(msg):
    import re
    s = str(msg)
    for name, pat in COQ_ERROR_RULES:
        if re.search(pat, s, re.IGNORECASE | re.MULTILINE):
            return name
    return "uncategorised"


# ------------------------------------------------------------------

def build_items():
    rows = []
    for path in C.coq_files():
        md, results = C.read_coq_file(path)
        tier = md.get("prompt_tier") or md.get("tier") or _tier_from_name(path)
        model = md.get("model") or _field_from_name(path, 1)
        dataset = md.get("dataset") or _field_from_name(path, 0) or "fracas"
        condition = md.get("condition") or "c1"
        for it in results:
            errs = it.get("errors") or []
            cats = sorted({classify_coq_error(e) for e in errs})
            n = C.item_number(it.get("id"))
            rows.append({
                "dataset": dataset, "model": model, "tier": tier,
                "condition": condition,
                "id": it.get("id"),
                "gold": "|".join(sorted(C.label_set(it.get("gold")))),
                "predicted_label": it.get("predicted_label"),
                "compiled": bool(it.get("compiled")),
                "proof_complete": bool(it.get("proof_complete")),
                "correct": bool(it.get("correct")),
                "attempts": it.get("attempts"),
                "n_errors": len(errs),
                "error_category": "|".join(cats),
                "section": C.fracas_section_from_number(n),
            })
    return pd.DataFrame(rows, columns=ITEM_COLS)


def _tier_from_name(path):
    import re
    m = re.search(r"__(T[0-3])__|_(T[0-3])_", Path(path).name)
    return (m.group(1) or m.group(2)) if m else ""


def _field_from_name(path, idx):
    parts = Path(path).stem.split("__")
    return parts[idx] if len(parts) > idx else ""


def build_summary(items):
    if items.empty:
        return pd.DataFrame(columns=SUMMARY_COLS)
    rows = []
    for (ds, m, tier, cond), g in items.groupby(
            ["dataset", "model", "tier", "condition"], observed=True):
        n = len(g)
        n_comp = int(g.compiled.sum())
        rows.append({
            "dataset": ds, "model": m, "tier": tier, "condition": cond,
            "n_items": n,
            "n_compiled": n_comp,
            "n_proved": int(g.proof_complete.sum()),
            "n_correct": int(g.correct.sum()),
            "compilation_rate": n_comp / n if n else np.nan,
            "proof_rate": float(g.proof_complete.mean()) if n else np.nan,
            "accuracy": float(g.correct.mean()) if n else np.nan,
            "accuracy_given_compiled": (float(g[g.compiled].correct.mean())
                                        if n_comp else np.nan),
            "mean_attempts": float(pd.to_numeric(g.attempts,
                                                 errors="coerce").mean()),
            "path": "",
        })
    return pd.DataFrame(rows, columns=SUMMARY_COLS)


def build_by_tier(summary):
    if summary.empty:
        return pd.DataFrame(columns=["tier", "n_files", "n_items",
                                     "compilation_rate", "proof_rate",
                                     "accuracy", "mean_attempts"])
    g = summary.groupby("tier", observed=True).agg(
        n_files=("model", "size"),
        n_items=("n_items", "sum"),
        compilation_rate=("compilation_rate", "mean"),
        proof_rate=("proof_rate", "mean"),
        accuracy=("accuracy", "mean"),
        mean_attempts=("mean_attempts", "mean"),
    ).reset_index()
    return g


def build_attempts(items):
    if items.empty:
        return pd.DataFrame(columns=["tier", "attempts", "n_items", "share"])
    rows = []
    for tier, g in items.groupby("tier", observed=True):
        vc = pd.to_numeric(g.attempts, errors="coerce").value_counts().sort_index()
        for a, n in vc.items():
            rows.append({"tier": tier, "attempts": a, "n_items": int(n),
                         "share": float(n / len(g))})
    return pd.DataFrame(rows)


def build_error_taxonomy(items):
    if items.empty:
        return pd.DataFrame(columns=["tier", "category", "n_items", "share"])
    rows = []
    for tier, g in items.groupby("tier", observed=True):
        counter = Counter()
        for cats in g.error_category:
            for c in str(cats).split("|"):
                if c:
                    counter[c] += 1
        for cat, n in counter.most_common():
            rows.append({"tier": tier, "category": cat, "n_items": n,
                         "share": n / len(g)})
    return pd.DataFrame(rows)


def build_by_section(items):
    if items.empty:
        return pd.DataFrame(columns=["tier", "section", "section_name",
                                     "n_items", "compilation_rate",
                                     "proof_rate", "accuracy"])
    s = items.dropna(subset=["section"])
    rows = []
    for (tier, sec), g in s.groupby(["tier", "section"], observed=True):
        rows.append({
            "tier": tier, "section": int(sec),
            "section_name": C.SECTION_NAME.get(int(sec), "?"),
            "n_items": len(g),
            "compilation_rate": float(g.compiled.mean()),
            "proof_rate": float(g.proof_complete.mean()),
            "accuracy": float(g.correct.mean()),
        })
    return pd.DataFrame(rows)


# ------------------------------------------------------------------
# Figures
# ------------------------------------------------------------------

def _placeholder(msg):
    fig, ax = plt.subplots(figsize=(5.2, 2.2))
    ax.text(0.5, 0.5, msg, ha="center", va="center", fontsize=8,
            color="0.3", wrap=True, transform=ax.transAxes)
    ax.set_axis_off()
    return fig


def fig_compilation_by_tier(summary):
    if summary.empty:
        return _placeholder(
            "No post-fix Coq runs yet.\nRun phase2_coq/coq_pipeline.py per "
            "RUN_COQ.md, then re-run this script.")
    m = summary.pivot_table(index="model", columns="tier",
                            values="compilation_rate", observed=True)
    m = m.reindex(index=[x for x in C.MODELS if x in m.index],
                  columns=[t for t in TIERS if t in m.columns])
    fig, ax = plt.subplots(figsize=(5.0, 3.2))
    x = np.arange(len(m.index))
    w = 0.8 / max(len(m.columns), 1)
    shades = ["#1f4e79", "#41729f", "#7ba0c4", "#b9d3e6"]
    for k, tier in enumerate(m.columns):
        ax.bar(x + (k - (len(m.columns) - 1) / 2) * w, m[tier], width=w,
               color=shades[k % len(shades)], label=tier,
               edgecolor="white", linewidth=0.4)
    ax.set_xticks(x)
    ax.set_xticklabels(list(m.index), rotation=30, ha="right")
    ax.set_ylabel("compilation rate")
    ax.set_ylim(0, 1)
    ax.set_title("Coq compilation rate by prompt tier")
    ax.legend(frameon=False, title="tier", fontsize=6, title_fontsize=6)
    return fig


def fig_error_taxonomy(tax):
    if tax.empty:
        return _placeholder("No post-fix Coq runs yet: no coqc error data.")
    piv = tax.pivot_table(index="category", columns="tier", values="n_items",
                          observed=True, aggfunc="sum").fillna(0)
    piv = piv.loc[piv.sum(axis=1).sort_values().index]
    fig, ax = plt.subplots(figsize=(5.8, 3.3))
    y = np.arange(len(piv))
    left = np.zeros(len(piv))
    shades = ["#1f4e79", "#41729f", "#7ba0c4", "#b9d3e6"]
    for k, tier in enumerate(piv.columns):
        ax.barh(y, piv[tier], left=left, height=0.66,
                color=shades[k % len(shades)], label=tier,
                edgecolor="white", linewidth=0.4)
        left = left + piv[tier].to_numpy()
    ax.set_yticks(y)
    ax.set_yticklabels([c.replace("_", " ") for c in piv.index])
    ax.set_xlabel("items with this coqc failure")
    ax.set_title("Why Coq formalisations fail to compile")
    ax.legend(frameon=False, title="tier", fontsize=6, title_fontsize=6)
    return fig


def fig_tier_comparison(bytier):
    if bytier.empty:
        return _placeholder(
            "No post-fix Coq runs yet.\nT0 vs T1 vs T2 comparison pending.")
    fig, ax = plt.subplots(figsize=(4.6, 3.0))
    x = np.arange(len(bytier))
    for col, colour, label, mk in (
            ("compilation_rate", FOCAL, "compiles", "o"),
            ("proof_rate", "#7ba05b", "proof completed", "s"),
            ("accuracy", "#b5651d", "label correct", "^")):
        ax.plot(x, bytier[col], marker=mk, color=colour, label=label, lw=1.2,
                ms=5)
    ax.set_xticks(x)
    ax.set_xticklabels(list(bytier.tier))
    ax.set_xlabel("prompt tier")
    ax.set_ylabel("rate")
    ax.set_ylim(0, 1)
    ax.set_title("Does formal context help? T0 to T2")
    ax.legend(frameon=False, fontsize=6)
    return fig


# ------------------------------------------------------------------

def main():
    C.ensure_dirs()
    print("Coq pipeline analysis")

    items = build_items()
    C.save_table(items, "coq_by_item.csv")

    summary = build_summary(items)
    C.save_table(summary, "coq_summary.csv")

    bytier = build_by_tier(summary)
    C.save_table(bytier, "coq_by_tier.csv")

    attempts = build_attempts(items)
    C.save_table(attempts, "coq_attempts.csv")

    tax = build_error_taxonomy(items)
    C.save_table(tax, "coq_error_taxonomy.csv")

    bysec = build_by_section(items)
    C.save_table(bysec, "coq_by_section.csv")

    C.save_fig(fig_compilation_by_tier(summary), "coq_compilation_by_tier.png")
    C.save_fig(fig_error_taxonomy(tax), "coq_error_taxonomy.png")
    C.save_fig(fig_tier_comparison(bytier), "coq_tier_comparison.png")

    files = C.coq_files()
    print(f"\n  post-fix Coq result files: {len(files)}")
    if items.empty:
        print("  no items: tables written with headers only.")
        print("  -> run the pipeline per RUN_COQ.md, then re-run this script.")
    else:
        print(f"  items: {len(items)}")
        print(f"  compilation rate: {items.compiled.mean():.3f}")
        print(f"  proof rate:       {items.proof_complete.mean():.3f}")
        print(f"  accuracy:         {items.correct.mean():.3f}")
        for _, r in bytier.iterrows():
            print(f"    {r.tier}: compile={r.compilation_rate:.3f} "
                  f"proof={r.proof_rate:.3f} acc={r.accuracy:.3f}")
    return items


if __name__ == "__main__":
    main()
