"""Phase 2a FOL pipeline: accuracy, decision-tree outcomes, error taxonomy.

Reads phase2_fol/results/{dataset}/{dataset}__{model}__c1.json (43 files,
23,670 items) and writes:

  tables/fol_accuracy.csv         per file: accuracy, label mix, attempts
  tables/fol_accuracy_wide.csv    model x dataset accuracy matrix
  tables/fol_error_taxonomy.csv   error categories with counts and shares
  tables/fol_error_examples.csv   one verbatim example per category
  tables/fol_confusion.csv        gold x predicted, pooled per dataset
  tables/fol_decision_tree.csv    steps_detail outcome patterns
  tables/fol_by_item.csv          tidy per-item table (feeds cross_pipeline)

  figs/fol_accuracy_heatmap.png
  figs/fol_error_taxonomy.png
  figs/fol_confusion.png
  figs/fol_vs_phase1.png

The decision tree the pipeline implements:
  Phase A  Prover9 P |- H            -> Entailment
  Phase B  Prover9 P |- ~H           -> Contradiction
  Phase C  MACE4 P & ~H satisfiable
  Phase D  MACE4 P & H satisfiable
  C and D both satisfied             -> Unknown
  neither                            -> Undecided

Note the label vocabulary has a fourth value, `Undecided`, which is a
pipeline outcome rather than an NLI class; it is never correct against
gold and is reported separately.

Usage:  python analysis/fol_analysis.py
"""

from __future__ import annotations

import re
import sys
from collections import Counter, defaultdict
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

# ------------------------------------------------------------------
# Error taxonomy
# ------------------------------------------------------------------
# Categories are derived from the verbatim Prover9/MACE4 and pipeline
# messages present in the data, checked in order. `fol_error_examples.csv`
# carries one real message per category so the mapping is auditable.

ERROR_RULES = [
    ("llm_timeout",
     r"APITimeoutError|Request timed out|<LLM call failed.*[Tt]imeout"),
    ("llm_call_failed",
     r"<LLM call failed"),
    ("prover_timeout",
     r"\bTIMEOUT\b|max_seconds|time limit|Prover9 timed out"),
    ("parse_failure",
     r"Parse error: could not extract"),
    ("arity_conflict",
     r"used with multiple arities"),
    ("relation_function_clash",
     r"used as both relation and function symbols"),
    ("variable_as_atom",
     r"cannot be used as atomic formulas, because they are variables"),
    ("term_construction",
     r"A term cannot be constructed from the marked string"),
    ("syntax_other",
     r"Syntax error|%%ERROR"),
    ("empty_output",
     r"^\s*$|Empty"),
]


def classify_error(msg):
    """Map one raw error string onto a taxonomy category."""
    s = str(msg)
    for name, pat in ERROR_RULES:
        if re.search(pat, s, re.IGNORECASE | re.MULTILINE):
            return name
    return "uncategorised"


# ------------------------------------------------------------------
# Per-item table
# ------------------------------------------------------------------

def build_items():
    rows = []
    for info, md, items in C.iter_fol():
        for it in items:
            pred = it.get("label")
            strict, partial = C.correctness(pred, it.get("gold"))
            sd = it.get("steps_detail") or {}
            errs = it.get("errors") or []
            cats = sorted({classify_error(e) for e in errs})
            rows.append({
                "dataset": info["dataset"],
                "model": info["model"],
                "id": it.get("id"),
                "language": it.get("language"),
                "gold": "|".join(sorted(C.label_set(it.get("gold")))),
                "fol_label": pred,
                "is_undecided": pred == "Undecided",
                "strict_correct": strict,
                "partial_correct": partial,
                "success_flag": bool(it.get("success")),
                "attempts": it.get("attempts"),
                "n_errors": len(errs),
                "error_categories": "|".join(cats),
                "entailment_proved": bool(sd.get("entailment_proved")),
                "contradiction_proved": bool(sd.get("contradiction_proved")),
                "entailment_refuted": bool(sd.get("entailment_refuted")),
                "contradiction_refuted": bool(sd.get("contradiction_refuted")),
                "sections": "|".join(
                    str(x) for x in C.sections_of(it, info["dataset"])),
            })
    return pd.DataFrame(rows)


def build_accuracy(items):
    rows = []
    for (ds, m), g in items.groupby(["dataset", "model"], observed=True):
        n = len(g)
        rows.append({
            "dataset": ds, "model": m, "n_items": n,
            "n_correct": int(g.strict_correct.fillna(False).sum()),
            "accuracy": float(g.strict_correct.fillna(False).mean()),
            "n_undecided": int(g.is_undecided.sum()),
            "undecided_rate": float(g.is_undecided.mean()),
            "n_entailment": int((g.fol_label == "Entailment").sum()),
            "n_contradiction": int((g.fol_label == "Contradiction").sum()),
            "n_unknown": int((g.fol_label == "Unknown").sum()),
            "mean_attempts": float(pd.to_numeric(g.attempts,
                                                 errors="coerce").mean()),
            "n_items_with_errors": int((g.n_errors > 0).sum()),
            "error_rate": float((g.n_errors > 0).mean()),
            # accuracy restricted to items the pipeline actually decided
            "accuracy_decided": float(
                g[~g.is_undecided].strict_correct.fillna(False).mean())
            if (~g.is_undecided).any() else np.nan,
        })
    df = pd.DataFrame(rows)
    df["dataset"] = pd.Categorical(df["dataset"], C.DATASETS, ordered=True)
    df["model"] = pd.Categorical(df["model"], C.MODELS, ordered=True)
    return df.sort_values(["dataset", "model"])


def build_error_taxonomy(items_raw_counter, total_errors, total_items,
                         items_with_error):
    rows = []
    for cat, n in items_raw_counter.most_common():
        rows.append({
            "category": cat,
            "n_error_messages": n,
            "share_of_error_messages": n / total_errors if total_errors else np.nan,
        })
    df = pd.DataFrame(rows)
    df.attrs["total_errors"] = total_errors
    df.attrs["total_items"] = total_items
    df.attrs["items_with_error"] = items_with_error
    return df


def collect_errors():
    """Count error messages by category and keep one example of each."""
    counter = Counter()
    examples = {}
    per_item_cat = Counter()
    total_items = 0
    items_with_error = 0
    for info, md, items in C.iter_fol():
        for it in items:
            total_items += 1
            errs = it.get("errors") or []
            if errs:
                items_with_error += 1
            cats_here = set()
            for e in errs:
                cat = classify_error(e)
                counter[cat] += 1
                cats_here.add(cat)
                examples.setdefault(cat, str(e)[:400])
            for c in cats_here:
                per_item_cat[c] += 1
    return counter, examples, per_item_cat, total_items, items_with_error


def build_confusion(items):
    rows = []
    for ds, g in items.groupby("dataset", observed=True):
        for gold in C.LABELS:
            sub = g[g.gold == gold]
            row = {"dataset": ds, "gold": gold, "gold_total": len(sub)}
            for p in C.LABELS + ["Undecided"]:
                n = int((sub.fol_label == p).sum())
                row[f"pred_{p}"] = n
                row[f"frac_{p}"] = n / len(sub) if len(sub) else np.nan
            rows.append(row)
    return pd.DataFrame(rows)


def build_decision_tree(items):
    """Frequency of each steps_detail flag pattern and its resulting label."""
    cols = ["entailment_proved", "contradiction_proved",
            "entailment_refuted", "contradiction_refuted"]
    g = items.groupby(cols + ["fol_label"], observed=True).size(
        ).reset_index(name="n")
    g["share"] = g.n / g.n.sum()
    g["accuracy_in_pattern"] = [
        float(items[(items[cols[0]] == r[cols[0]]) &
                    (items[cols[1]] == r[cols[1]]) &
                    (items[cols[2]] == r[cols[2]]) &
                    (items[cols[3]] == r[cols[3]]) &
                    (items.fol_label == r.fol_label)]
              .strict_correct.fillna(False).mean())
        for _, r in g.iterrows()]
    return g.sort_values("n", ascending=False)


# ------------------------------------------------------------------
# Figures
# ------------------------------------------------------------------

def fig_accuracy_heatmap(acc):
    m = acc.pivot_table(index="model", columns="dataset", values="accuracy",
                        observed=True)
    m = m.reindex(index=[x for x in C.MODELS if x in m.index],
                  columns=[d for d in C.DATASETS if d in m.columns])
    fig, ax = plt.subplots(figsize=(5.2, 3.4))
    vmin, vmax = float(np.nanmin(m.values)), float(np.nanmax(m.values))
    mid = (vmin + vmax) / 2
    im = ax.imshow(m.values, cmap="viridis", vmin=vmin, vmax=vmax, aspect="auto")
    ax.set_xticks(range(m.shape[1]))
    ax.set_xticklabels([C.DATASET_DISPLAY[c] for c in m.columns], rotation=30,
                       ha="right")
    ax.set_yticks(range(m.shape[0]))
    ax.set_yticklabels(list(m.index))
    for i in range(m.shape[0]):
        for j in range(m.shape[1]):
            v = m.values[i, j]
            if np.isfinite(v):
                ax.text(j, i, f"{v:.2f}", ha="center", va="center", fontsize=6,
                        color="white" if v < mid else "black")
    ax.set_title("FOL pipeline accuracy (NL to FOL to Prover9/MACE4)")
    ax.grid(False)
    cb = fig.colorbar(im, ax=ax, fraction=0.035, pad=0.02)
    cb.set_label("accuracy (higher = better)", fontsize=6)
    cb.ax.tick_params(labelsize=6)
    return fig


def fig_error_taxonomy(tax, per_item_cat, total_items):
    s = tax[tax.category != "uncategorised"].copy()
    s = s.sort_values("n_error_messages")
    fig, ax = plt.subplots(figsize=(5.8, 3.3))
    y = np.arange(len(s))
    ax.barh(y, s.n_error_messages, color=FOCAL, height=0.66,
            edgecolor="white", linewidth=0.4)
    ax.set_yticks(y)
    ax.set_yticklabels([c.replace("_", " ") for c in s.category])
    ax.set_xlabel("error messages")
    top = s.iloc[-1]
    ax.annotate(f"{int(top.n_error_messages)} "
                f"({top.share_of_error_messages:.0%} of all messages)",
                (top.n_error_messages, len(s) - 1),
                textcoords="offset points", xytext=(-6, 0), fontsize=6,
                ha="right", va="center", color="white")
    ax.set_title("FOL failures are dominated by predicate-signature errors,\n"
                 "not by semantic gaps")
    ax.margins(x=0.04)
    return fig


def fig_confusion(conf):
    """Row-normalised gold x predicted, one panel per dataset."""
    dss = [d for d in C.DATASETS if d in set(conf.dataset)]
    fig, axes = plt.subplots(1, len(dss), figsize=(2.05 * len(dss), 2.5),
                             sharey=True)
    preds = C.LABELS + ["Undecided"]
    for k, (ax, ds) in enumerate(zip(np.atleast_1d(axes), dss)):
        sub = conf[conf.dataset == ds].set_index("gold")
        m = np.array([[sub.loc[g, f"frac_{p}"] for p in preds]
                      for g in C.LABELS], dtype=float)
        im = ax.imshow(m, cmap="viridis", vmin=0, vmax=1, aspect="auto")
        ax.set_xticks(range(len(preds)))
        ax.set_xticklabels(["Ent", "Con", "Unk", "Und"], rotation=0, fontsize=6)
        if k == 0:
            ax.set_yticks(range(len(C.LABELS)))
            ax.set_yticklabels(C.LABELS, fontsize=6)
            ax.set_ylabel("gold")
        ax.set_title(C.DATASET_DISPLAY[ds], fontsize=7)
        for i in range(m.shape[0]):
            for j in range(m.shape[1]):
                if np.isfinite(m[i, j]):
                    ax.text(j, i, f"{m[i, j]:.2f}", ha="center", va="center",
                            fontsize=5, color="white" if m[i, j] < 0.5 else "black")
        ax.grid(False)
    fig.supxlabel("FOL pipeline label (Und = Undecided)", fontsize=7)
    fig.suptitle("Gold vs FOL label, row-normalised: Contradiction is "
                 "systematically under-produced", fontsize=8)
    fig.tight_layout()
    return fig


def fig_fol_vs_phase1(acc):
    """FOL accuracy against the same model's direct Phase 1 accuracy."""
    p1 = pd.read_csv(C.OUT_TABLES / "phase1_accuracy.csv")
    p1 = p1[(p1.technique == "zero-shot") & (p1.language == "en")]
    j = acc.merge(p1[["dataset", "model", "strict_accuracy"]],
                  on=["dataset", "model"], how="inner")
    fig, ax = plt.subplots(figsize=(4.4, 3.4))
    for ds, g in j.groupby("dataset", observed=True):
        ax.scatter(g.strict_accuracy, g.accuracy, s=26,
                   label=C.DATASET_DISPLAY[ds], edgecolor="white", linewidth=0.5)
    lo, hi = 0.30, 0.85
    ax.plot([lo, hi], [lo, hi], ls="--", lw=0.8, color="0.55", zorder=1)
    ax.set_xlim(lo, hi)
    ax.set_ylim(lo, hi)
    ax.set_xlabel("Phase 1 direct-prediction accuracy")
    ax.set_ylabel("Phase 2a FOL accuracy")
    ax.set_title("Formalising through FOL costs accuracy\n"
                 "(points below the diagonal)")
    ax.legend(frameon=False, fontsize=6, loc="upper left")
    return fig


# ------------------------------------------------------------------

def main():
    C.ensure_dirs()
    print("FOL pipeline analysis")

    items = build_items()
    C.save_table(items, "fol_by_item.csv")

    acc = build_accuracy(items)
    C.save_table(acc, "fol_accuracy.csv")

    wide = acc.pivot_table(index="model", columns="dataset", values="accuracy",
                           observed=True)
    C.save_table(wide.reset_index(), "fol_accuracy_wide.csv")

    counter, examples, per_item_cat, total_items, items_with_error = collect_errors()
    total_errors = sum(counter.values())
    tax = build_error_taxonomy(counter, total_errors, total_items,
                               items_with_error)
    tax["n_items_affected"] = [per_item_cat[c] for c in tax.category]
    tax["share_of_items"] = tax.n_items_affected / total_items
    C.save_table(tax, "fol_error_taxonomy.csv")
    C.save_table(pd.DataFrame(
        [{"category": k, "example_message": v} for k, v in sorted(examples.items())]),
        "fol_error_examples.csv")

    conf = build_confusion(items)
    C.save_table(conf, "fol_confusion.csv")

    tree = build_decision_tree(items)
    C.save_table(tree, "fol_decision_tree.csv")

    C.save_fig(fig_accuracy_heatmap(acc), "fol_accuracy_heatmap.png")
    C.save_fig(fig_error_taxonomy(tax, per_item_cat, total_items),
               "fol_error_taxonomy.png")
    C.save_fig(fig_confusion(conf), "fol_confusion.png")
    if (C.OUT_TABLES / "phase1_accuracy.csv").exists():
        C.save_fig(fig_fol_vs_phase1(acc), "fol_vs_phase1.png")

    print(f"\n  files read: {len(C.fol_files())}")
    print(f"  items: {total_items}")
    print(f"  items with >=1 error: {items_with_error} "
          f"({items_with_error/total_items:.1%})")
    print(f"  error messages: {total_errors}")
    print(f"  overall accuracy: {items.strict_correct.fillna(False).mean():.4f}")
    print(f"  undecided rate:   {items.is_undecided.mean():.4f}")
    print("  top error categories (share of messages):")
    for _, r in tax.head(5).iterrows():
        print(f"    {r.category:26s} {r.n_error_messages:6d}  "
              f"{r.share_of_error_messages:.1%}")
    return items


if __name__ == "__main__":
    main()
