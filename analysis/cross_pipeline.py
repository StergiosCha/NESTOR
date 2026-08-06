"""Cross-pipeline comparison: Phase 1 vs judge scores vs FOL vs Coq.

Joins the three pipelines per item (dataset, model, id) and asks:

  * which items does direct prediction get right that FOL gets wrong,
    and vice versa
  * does explanation quality predict formalisation success
  * where does the Coq pipeline sit relative to FOL, once runs exist

  tables/cross_pipeline.csv          per-item join
  tables/cross_pipeline_summary.csv  per model x dataset agreement counts
  tables/cross_quality_vs_fol.csv    FOL success rate by judge score
  tables/cross_correlations.csv      point-biserial / Spearman correlations

  figs/cross_pipeline_correlation.png
  figs/cross_pipeline_flow.png

Usage:  python analysis/cross_pipeline.py
"""

from __future__ import annotations

import sys
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
from scipy import stats

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
COMPARATOR = "#9bb8d3"
ALARM = "#b5651d"


def _norm_id(x):
    """Canonical join key: dataset prefix + zero-padded number.

    Phase 1 / judge / FOL all use the zero-padded form, but the Coq
    pipeline's loader emits 'fracas-1'. Reducing both to the integer
    makes the join robust.
    """
    n = C.item_number(x)
    return n if n is not None else str(x)


def load_phase1_items():
    rows = []
    for info, md, items in C.iter_phase1(technique="zero-shot", language="en"):
        for it in items:
            s, p = C.correctness(it.get("predicted"), it.get("gold"))
            rows.append({
                "dataset": info["dataset"],
                "model": info["model"],
                "key": _norm_id(it.get("id")),
                "id": it.get("id"),
                "gold": "|".join(sorted(C.label_set(it.get("gold")))),
                "p1_correct": s,
                "p1_label": "|".join(sorted(C.label_set(it.get("predicted")))),
                "sections": "|".join(str(x) for x in C.sections_of(it, info["dataset"])),
            })
    return pd.DataFrame(rows)


def load_judge_items():
    p = C.OUT_TABLES / "judge_scores_by_item.csv"
    if not p.exists():
        return pd.DataFrame(columns=["dataset", "model", "key"])
    df = pd.read_csv(p)
    df["key"] = df["id"].map(_norm_id)
    return df[["dataset", "model", "key", "phenomenon_id", "soundness",
               "consistency", "total"]]


def load_fol_items():
    p = C.OUT_TABLES / "fol_by_item.csv"
    if not p.exists():
        return pd.DataFrame(columns=["dataset", "model", "key"])
    df = pd.read_csv(p)
    df["key"] = df["id"].map(_norm_id)
    return df[["dataset", "model", "key", "fol_label", "strict_correct",
               "is_undecided", "n_errors", "error_categories"]].rename(
        columns={"strict_correct": "fol_correct"})


def load_coq_items():
    """Per-item Coq outcomes, empty until the fixed pipeline has been run."""
    rows = []
    for path in C.coq_files():
        md, results = C.read_coq_file(path)
        tier = md.get("prompt_tier") or md.get("tier") or ""
        model = md.get("model") or ""
        dataset = md.get("dataset") or "fracas"
        for it in results:
            rows.append({
                "dataset": dataset,
                "model": model,
                "tier": tier,
                "key": _norm_id(it.get("id")),
                "coq_compiled": bool(it.get("compiled")),
                "coq_proved": bool(it.get("proof_complete")),
                "coq_correct": bool(it.get("correct")),
                "coq_label": it.get("predicted_label"),
                "coq_attempts": it.get("attempts"),
            })
    return pd.DataFrame(rows)


# ------------------------------------------------------------------

def build_join():
    p1 = load_phase1_items()
    jd = load_judge_items()
    fol = load_fol_items()
    df = p1.merge(jd, on=["dataset", "model", "key"], how="left")
    df = df.merge(fol, on=["dataset", "model", "key"], how="left")
    coq = load_coq_items()
    if not coq.empty:
        df = df.merge(coq, on=["dataset", "model", "key"], how="left")
    else:
        for c in ("tier", "coq_compiled", "coq_proved", "coq_correct",
                  "coq_label", "coq_attempts"):
            df[c] = np.nan
    return df


def build_summary(df):
    rows = []
    for (ds, m), g in df.groupby(["dataset", "model"], observed=True):
        both = g.dropna(subset=["p1_correct", "fol_correct"])
        n = len(both)
        if n == 0:
            continue
        p1c = both.p1_correct.astype(bool)
        folc = both.fol_correct.astype(bool)
        rows.append({
            "dataset": ds, "model": m, "n_joined": n,
            "p1_accuracy": float(p1c.mean()),
            "fol_accuracy": float(folc.mean()),
            "both_correct": int((p1c & folc).sum()),
            "p1_only": int((p1c & ~folc).sum()),
            "fol_only": int((~p1c & folc).sum()),
            "neither": int((~p1c & ~folc).sum()),
            "p1_only_rate": float((p1c & ~folc).mean()),
            "fol_only_rate": float((~p1c & folc).mean()),
            "fol_undecided_rate": float(both.is_undecided.astype(bool).mean()),
        })
    return pd.DataFrame(rows)


def build_quality_vs_fol(df):
    """FOL success rate conditioned on the judge's explanation scores."""
    rows = []
    sub = df.dropna(subset=["phenomenon_id", "fol_correct"])
    for crit in ("phenomenon_id", "soundness", "consistency", "total"):
        s = df.dropna(subset=[crit, "fol_correct"])
        for val, g in s.groupby(crit):
            rows.append({
                "criterion": crit,
                "score": val,
                "n_items": len(g),
                "fol_accuracy": float(g.fol_correct.astype(bool).mean()),
                "fol_undecided_rate": float(g.is_undecided.astype(bool).mean()),
                "p1_accuracy": float(g.p1_correct.astype(bool).mean()),
            })
    return pd.DataFrame(rows), sub


def build_correlations(df):
    """Item-level and aggregate associations between the pipelines."""
    rows = []
    sub = df.dropna(subset=["phenomenon_id", "fol_correct"])
    if len(sub) > 10:
        for crit in ("phenomenon_id", "soundness", "consistency", "total"):
            s = df.dropna(subset=[crit, "fol_correct"])
            x = s[crit].astype(float).to_numpy()
            y = s.fol_correct.astype(bool).astype(int).to_numpy()
            if len(set(y)) > 1 and len(set(x)) > 1:
                r, p = stats.pointbiserialr(y, x)
                rho, prho = stats.spearmanr(x, y)
                rows.append({
                    "comparison": f"judge_{crit} vs FOL correctness",
                    "level": "item",
                    "n": len(s),
                    "statistic": "point-biserial r",
                    "estimate": r, "p_value": p,
                    "spearman_rho": rho, "spearman_p": prho,
                })
        # explanation quality vs whether FOL could decide at all
        for crit in ("phenomenon_id", "soundness"):
            s = df.dropna(subset=[crit, "is_undecided"])
            x = s[crit].astype(float).to_numpy()
            y = s.is_undecided.astype(bool).astype(int).to_numpy()
            if len(set(y)) > 1 and len(set(x)) > 1:
                r, p = stats.pointbiserialr(y, x)
                rows.append({
                    "comparison": f"judge_{crit} vs FOL undecided",
                    "level": "item", "n": len(s),
                    "statistic": "point-biserial r",
                    "estimate": r, "p_value": p,
                    "spearman_rho": np.nan, "spearman_p": np.nan,
                })
    # aggregate: model-level Phase 1 vs FOL accuracy
    summ = build_summary(df)
    if len(summ) > 3:
        r, p = stats.pearsonr(summ.p1_accuracy, summ.fol_accuracy)
        rho, prho = stats.spearmanr(summ.p1_accuracy, summ.fol_accuracy)
        rows.append({
            "comparison": "Phase 1 accuracy vs FOL accuracy",
            "level": "model x dataset", "n": len(summ),
            "statistic": "Pearson r", "estimate": r, "p_value": p,
            "spearman_rho": rho, "spearman_p": prho,
        })
    return pd.DataFrame(rows)


# ------------------------------------------------------------------
# Figures
# ------------------------------------------------------------------

def fig_correlation(qvf, df):
    """FOL accuracy as a function of judge phenomenon_id and soundness."""
    fig, axes = plt.subplots(1, 2, figsize=(6.2, 2.9), sharey=True)
    for ax, crit in zip(axes, ["phenomenon_id", "soundness"]):
        s = qvf[qvf.criterion == crit].sort_values("score")
        ax.bar(s.score.astype(str), s.fol_accuracy, color=FOCAL, width=0.6,
               edgecolor="white", linewidth=0.4)
        for xi, (_, r) in enumerate(s.iterrows()):
            ax.text(xi, r.fol_accuracy + 0.012, f"{r.fol_accuracy:.2f}",
                    ha="center", fontsize=6)
            ax.text(xi, 0.02, f"n={int(r.n_items)}", ha="center", fontsize=5.5,
                    color="white")
        ax.set_xlabel(f"judge {crit.replace('_',' ')} score")
        ax.set_ylim(0, 1)
        ax.set_title(crit.replace("_", " "), fontsize=7)
    axes[0].set_ylabel("FOL pipeline accuracy")
    fig.suptitle("Explanation quality barely moves FOL formalisation success",
                 fontsize=8)
    fig.tight_layout()
    return fig


def fig_flow(summ):
    """Per-dataset breakdown of which pipeline solves which items."""
    g = summ.groupby("dataset", observed=True)[
        ["both_correct", "p1_only", "fol_only", "neither"]].sum()
    g = g.reindex([d for d in C.DATASETS if d in g.index])
    frac = g.div(g.sum(axis=1), axis=0)
    fig, ax = plt.subplots(figsize=(5.6, 3.0))
    left = np.zeros(len(frac))
    parts = [
        ("both_correct", "#2c5f8a", "both correct"),
        ("p1_only", COMPARATOR, "direct prediction only"),
        ("fol_only", "#7ba05b", "FOL only"),
        ("neither", "#c8c8c8", "neither"),
    ]
    y = np.arange(len(frac))
    for col, colour, label in parts:
        ax.barh(y, frac[col], left=left, color=colour, height=0.62,
                label=label, edgecolor="white", linewidth=0.4)
        for yi, (v, l) in enumerate(zip(frac[col], left)):
            if v > 0.06:
                ax.text(l + v / 2, yi, f"{v:.0%}", ha="center", va="center",
                        fontsize=6,
                        color="white" if col in ("both_correct",) else "0.15")
        left = left + frac[col].to_numpy()
    ax.set_yticks(y)
    ax.set_yticklabels([C.DATASET_DISPLAY[d] for d in frac.index])
    ax.set_xlabel("share of items (pooled over the 9 models)")
    ax.set_xlim(0, 1)
    ax.set_title("Direct prediction solves many items the FOL pipeline loses")
    # Legend below the axes: with five full-width stacked bars there is no
    # in-axes region free of data, so an inset legend covers the bars.
    ax.legend(frameon=False, fontsize=6, ncols=4,
              loc="upper center", bbox_to_anchor=(0.5, -0.18))
    fig.subplots_adjust(bottom=0.28)
    return fig


# ------------------------------------------------------------------

def main():
    C.ensure_dirs()
    print("Cross-pipeline analysis")

    df = build_join()
    C.save_table(df, "cross_pipeline.csv")

    summ = build_summary(df)
    C.save_table(summ, "cross_pipeline_summary.csv")

    qvf, sub = build_quality_vs_fol(df)
    C.save_table(qvf, "cross_quality_vs_fol.csv")

    corr = build_correlations(df)
    C.save_table(corr, "cross_correlations.csv")

    C.save_fig(fig_correlation(qvf, df), "cross_pipeline_correlation.png")
    C.save_fig(fig_flow(summ), "cross_pipeline_flow.png")

    tot = summ[["both_correct", "p1_only", "fol_only", "neither"]].sum()
    n = int(tot.sum())
    print(f"\n  joined items (zero-shot EN x 9 models): {n}")
    print(f"  both correct:            {int(tot.both_correct)} ({tot.both_correct/n:.1%})")
    print(f"  direct prediction only:  {int(tot.p1_only)} ({tot.p1_only/n:.1%})")
    print(f"  FOL only:                {int(tot.fol_only)} ({tot.fol_only/n:.1%})")
    print(f"  neither:                 {int(tot.neither)} ({tot.neither/n:.1%})")
    print("\n  correlations:")
    for _, r in corr.iterrows():
        print(f"    {r.comparison:44s} n={int(r.n):6d} "
              f"{r.statistic}={r.estimate:+.3f} p={r.p_value:.2e}")
    n_coq = int(df.coq_compiled.notna().sum())
    print(f"\n  Coq items joined: {n_coq}"
          + ("  (no post-fix Coq runs yet)" if n_coq == 0 else ""))
    return df


if __name__ == "__main__":
    main()
