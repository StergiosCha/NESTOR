"""Explanation quality: LLM-as-judge scores, right-for-wrong-reasons, phenomena.

Reads phase1_nli_eval/judge_scores/ (zero-shot EN only, GPT-5.4 as judge)
and joins each scored item back to its Phase 1 prediction so that
prediction correctness and explanation quality can be crossed.

  tables/judge_scores.csv            per model x dataset mean criterion scores
  tables/judge_scores_by_item.csv    tidy per-item join (feeds cross_pipeline)
  tables/right_for_wrong_reasons.csv correct label but phenomenon_id = 0
  tables/judge_by_phenomenon.csv     mean scores per FraCaS section
  tables/judge_coverage.csv          which model x dataset cells are scored

  figs/judge_criteria.png
  figs/judge_by_phenomenon_heatmap.png
  figs/right_for_wrong_reasons.png

Scoring rubric: phenomenon_id 0-2, soundness 0-2, consistency 0-1,
total 0-5.

Usage:  python analysis/judge_analysis.py
"""

from __future__ import annotations

import sys
from collections import defaultdict
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

CRITERIA = ["phenomenon_id", "soundness", "consistency", "total"]
CRITERION_MAX = {"phenomenon_id": 2, "soundness": 2, "consistency": 1, "total": 5}
CRITERION_LABEL = {
    "phenomenon_id": "phenomenon identification (0-2)",
    "soundness": "soundness (0-2)",
    "consistency": "consistency (0-1)",
    "total": "total (0-5)",
}
FOCAL = "#1f4e79"


def _phase1_index(dataset, model):
    """{item_id: item} for the zero-shot EN Phase 1 file of this cell."""
    files = C.phase1_files(dataset=dataset, model=model,
                           technique="zero-shot", language="en")
    if not files:
        return {}
    d = C.load_json(files[0]["path"])
    return {it["id"]: it for it in d.get("results", [])}


# ------------------------------------------------------------------
# Per-item tidy table
# ------------------------------------------------------------------

def build_items():
    rows = []
    for info, md, scores in C.iter_judge():
        p1 = _phase1_index(info["dataset"], info["model"])
        for s in scores:
            item = p1.get(s["id"], {})
            strict, partial = C.correctness(s.get("predicted", item.get("predicted")),
                                            s.get("gold", item.get("gold")))
            secs = C.sections_of(item, info["dataset"]) if item else []
            rows.append({
                "dataset": info["dataset"],
                "model": info["model"],
                "id": s["id"],
                "gold": "|".join(sorted(C.label_set(s.get("gold")))),
                "predicted": "|".join(sorted(C.label_set(s.get("predicted")))),
                "strict_correct": strict,
                "partial_correct": partial,
                "phenomenon_id": s.get("phenomenon_id"),
                "soundness": s.get("soundness"),
                "consistency": s.get("consistency"),
                "total": s.get("total"),
                "sections": "|".join(str(x) for x in secs),
                "judge_model": md.get("judge_model", ""),
            })
    df = pd.DataFrame(rows)
    for c in CRITERIA:
        df[c] = pd.to_numeric(df[c], errors="coerce")
    return df


# ------------------------------------------------------------------
# Aggregates
# ------------------------------------------------------------------

def build_summary(items):
    g = items.groupby(["dataset", "model"], observed=True)
    out = g.agg(
        n_scored=("id", "size"),
        phenomenon_id=("phenomenon_id", "mean"),
        soundness=("soundness", "mean"),
        consistency=("consistency", "mean"),
        total=("total", "mean"),
        accuracy=("strict_correct", "mean"),
    ).reset_index()
    # normalised score so criteria on different scales are comparable
    for c in ("phenomenon_id", "soundness", "consistency", "total"):
        out[f"{c}_norm"] = out[c] / CRITERION_MAX[c]
    return out.sort_values(["dataset", "model"])


def build_right_for_wrong(items):
    """Correct label with a failed or partial phenomenon identification.

    phenomenon_id == 0 means the judge found no correct identification of
    the licensing phenomenon at all, so a correct label there is not
    evidence of reasoning. The <2 variant is the looser reading.
    """
    rows = []
    for (ds, m), g in items.groupby(["dataset", "model"], observed=True):
        correct = g[g.strict_correct == True]  # noqa: E712
        n_c = len(correct)
        rows.append({
            "dataset": ds, "model": m,
            "n_scored": len(g),
            "n_correct": n_c,
            "n_correct_phen0": int((correct.phenomenon_id == 0).sum()),
            "n_correct_phen_lt2": int((correct.phenomenon_id < 2).sum()),
            "rfwr_rate_phen0": float((correct.phenomenon_id == 0).mean()) if n_c else np.nan,
            "rfwr_rate_phen_lt2": float((correct.phenomenon_id < 2).mean()) if n_c else np.nan,
            # the mirror case: wrong label but a well-identified phenomenon
            "n_incorrect_phen2": int((g[g.strict_correct == False].phenomenon_id == 2).sum()),  # noqa: E712
            "mean_phen_correct": float(correct.phenomenon_id.mean()) if n_c else np.nan,
            "mean_phen_incorrect": float(g[g.strict_correct == False].phenomenon_id.mean()) if (g.strict_correct == False).any() else np.nan,  # noqa: E712
        })
    return pd.DataFrame(rows).sort_values(["dataset", "model"])


def build_by_phenomenon(items):
    """Mean criterion scores per FraCaS section (items may carry several)."""
    acc = defaultdict(list)
    for _, r in items.iterrows():
        if not r["sections"]:
            continue
        for sec in str(r["sections"]).split("|"):
            if sec:
                acc[(r["dataset"], r["model"], int(sec))].append(r)
    rows = []
    for (ds, m, sec), rs in acc.items():
        sub = pd.DataFrame(rs)
        rows.append({
            "dataset": ds, "model": m, "section": sec,
            "section_name": C.SECTION_NAME.get(sec, "?"),
            "n_items": len(sub),
            "phenomenon_id": sub.phenomenon_id.mean(),
            "soundness": sub.soundness.mean(),
            "consistency": sub.consistency.mean(),
            "total": sub.total.mean(),
            "accuracy": sub.strict_correct.mean(),
        })
    return pd.DataFrame(rows).sort_values(["dataset", "model", "section"])


def build_coverage():
    """Which dataset x model cells have judge scores, and which are missing."""
    have = {(i["dataset"], i["model"]) for i in C.judge_files()}
    rows = [{"dataset": ds, "model": m, "scored": (ds, m) in have}
            for ds in C.DATASETS for m in C.MODELS]
    return pd.DataFrame(rows)


# ------------------------------------------------------------------
# Figures
# ------------------------------------------------------------------

def fig_criteria(summary):
    """Per-criterion model means, normalised to [0,1], pooled over datasets."""
    g = summary.groupby("model", observed=True)[
        [f"{c}_norm" for c in ("phenomenon_id", "soundness", "consistency")]
    ].mean()
    order = g["phenomenon_id_norm"].sort_values().index
    g = g.loc[order]
    fig, ax = plt.subplots(figsize=(5.6, 3.2))
    x = np.arange(len(g))
    w = 0.26
    colors = [FOCAL, "#6d9dc5", "#b9d3e6"]
    names = ["phenomenon identification", "soundness", "consistency"]
    for k, (col, colour, nm) in enumerate(
            zip(g.columns, colors, names)):
        ax.bar(x + (k - 1) * w, g[col], width=w, color=colour, label=nm,
               edgecolor="white", linewidth=0.4)
    ax.set_xticks(x)
    ax.set_xticklabels(list(g.index), rotation=30, ha="right")
    ax.set_ylabel("mean score / maximum")
    ax.set_ylim(0, 1)
    # Title states the ordering the data actually shows, computed here
    # rather than asserted: consistency is near-ceiling for every model,
    # while phenomenon identification and soundness sit well below it.
    gap = g["consistency_norm"].mean() - g[["phenomenon_id_norm",
                                            "soundness_norm"]].mean().mean()
    ax.set_title("Judges score consistency near ceiling but mark "
                 f"phenomenon\nidentification and soundness {gap:.0%} lower")
    ax.legend(frameon=False, loc="upper left", ncols=1)
    ax.margins(x=0.02)
    return fig


def fig_by_phenomenon(byphen):
    """Heatmap of mean phenomenon_id per section, FraCaS only."""
    s = byphen[byphen.dataset == "fracas"]
    m = s.pivot_table(index="model", columns="section", values="phenomenon_id",
                      observed=True)
    m = m.reindex(index=[x for x in C.MODELS if x in m.index])
    fig, ax = plt.subplots(figsize=(5.6, 3.3))
    vmin, vmax = float(np.nanmin(m.values)), float(np.nanmax(m.values))
    im = ax.imshow(m.values, cmap="viridis", vmin=vmin, vmax=vmax, aspect="auto")
    mid = (vmin + vmax) / 2
    ax.set_xticks(range(m.shape[1]))
    ax.set_xticklabels([C.SECTION_SHORT.get(c, c) for c in m.columns],
                       rotation=40, ha="right")
    ax.set_yticks(range(m.shape[0]))
    ax.set_yticklabels(list(m.index))
    for i in range(m.shape[0]):
        for j in range(m.shape[1]):
            v = m.values[i, j]
            if np.isfinite(v):
                ax.text(j, i, f"{v:.1f}", ha="center", va="center", fontsize=5.5,
                        color="white" if v < mid else "black")
    ax.set_title("Phenomenon identification by FraCaS section (FraCaS, zero-shot EN)")
    ax.grid(False)
    cb = fig.colorbar(im, ax=ax, fraction=0.035, pad=0.02)
    cb.set_label("mean phenomenon_id (0-2)", fontsize=6)
    cb.ax.tick_params(labelsize=6)
    return fig


def fig_right_for_wrong(rfwr):
    """Rate of correct-label-but-phenomenon-missed, per model."""
    g = rfwr.groupby("model", observed=True)[
        ["rfwr_rate_phen0", "rfwr_rate_phen_lt2"]].mean().sort_values(
        "rfwr_rate_phen_lt2")
    fig, ax = plt.subplots(figsize=(5.4, 3.1))
    y = np.arange(len(g))
    ax.barh(y, g.rfwr_rate_phen_lt2, color="#b9d3e6", height=0.62,
            label="phenomenon only partly identified (<2)",
            edgecolor="white", linewidth=0.4)
    ax.barh(y, g.rfwr_rate_phen0, color=FOCAL, height=0.62,
            label="phenomenon not identified at all (=0)",
            edgecolor="white", linewidth=0.4)
    ax.set_yticks(y)
    ax.set_yticklabels(list(g.index))
    ax.set_xlabel("share of correctly-labelled items")
    ax.set_xlim(0, 1)
    ax.set_title("Right for the wrong reasons: correct labels whose\n"
                 "explanation misses the licensing phenomenon")
    ax.legend(frameon=False, loc="lower right")
    return fig


# ------------------------------------------------------------------

def main():
    C.ensure_dirs()
    print("Judge / explanation-quality analysis")

    items = build_items()
    C.save_table(items, "judge_scores_by_item.csv")

    summary = build_summary(items)
    C.save_table(summary, "judge_scores.csv")

    rfwr = build_right_for_wrong(items)
    C.save_table(rfwr, "right_for_wrong_reasons.csv")

    byphen = build_by_phenomenon(items)
    C.save_table(byphen, "judge_by_phenomenon.csv")

    cov = build_coverage()
    C.save_table(cov, "judge_coverage.csv")

    C.save_fig(fig_criteria(summary), "judge_criteria.png")
    C.save_fig(fig_by_phenomenon(byphen), "judge_by_phenomenon_heatmap.png")
    C.save_fig(fig_right_for_wrong(rfwr), "right_for_wrong_reasons.png")

    print(f"\n  judge files: {len(C.judge_files())}")
    print(f"  items scored: {len(items)}")
    print(f"  cells missing scores: {int((~cov.scored).sum())} of {len(cov)}")
    print("  mean phenomenon_id: "
          f"{items.phenomenon_id.mean():.3f} / 2")
    print(f"  mean soundness:     {items.soundness.mean():.3f} / 2")
    print(f"  mean consistency:   {items.consistency.mean():.3f} / 1")
    corr = items[items.strict_correct == True]  # noqa: E712
    print(f"  right-for-wrong-reasons (phen=0, pooled): "
          f"{(corr.phenomenon_id == 0).mean():.4f}")
    return items


if __name__ == "__main__":
    main()
