"""Judge validation: kappa between the LLM judge and human reviewers.

Reads reviews/ (20 files, 2 reviewers) and the judge scores, and computes
per-criterion agreement on the items both scored.

  tables/kappa.csv               kappa per criterion per comparison
  tables/kappa_by_file.csv       per review file, judge-vs-human
  tables/agreement_by_item.csv   tidy paired scores (auditable)
  tables/human_overlap.csv       which files two reviewers both scored

  figs/kappa_by_criterion.png
  figs/judge_vs_human_scatter.png

Statistics reported per criterion:
  * raw agreement (exact match)
  * Cohen's kappa (nominal)
  * quadratically weighted kappa -- the appropriate statistic for the
    ordinal 0/1/2 criteria, since it penalises a 0-vs-2 disagreement
    more than a 1-vs-2 one
  * Krippendorff-style mean absolute difference

Judge scores exist only for zero-shot EN, so few-shot review files can
only contribute to human-vs-human agreement.

Usage:  python analysis/agreement.py
"""

from __future__ import annotations

import sys
from collections import defaultdict
from itertools import combinations
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

CRITERIA = ["phenomenon_id", "soundness", "consistency"]
SCALE = {"phenomenon_id": [0, 1, 2], "soundness": [0, 1, 2],
         "consistency": [0, 1]}
FOCAL = "#1f4e79"
COMPARATOR = "#9bb8d3"


# ------------------------------------------------------------------
# Kappa
# ------------------------------------------------------------------

def cohen_kappa(a, b, categories, weights=None):
    """Cohen's kappa. weights=None -> nominal; 'quadratic' -> weighted.

    Implemented directly so the analysis has no sklearn dependency, and
    so the degenerate single-category case returns nan rather than 0.
    """
    a = np.asarray(a)
    b = np.asarray(b)
    if len(a) == 0:
        return np.nan
    k = len(categories)
    idx = {c: i for i, c in enumerate(categories)}
    O = np.zeros((k, k))
    for x, y in zip(a, b):
        if x in idx and y in idx:
            O[idx[x], idx[y]] += 1
    n = O.sum()
    if n == 0:
        return np.nan
    O = O / n
    row = O.sum(axis=1)
    col = O.sum(axis=0)
    E = np.outer(row, col)
    if weights == "quadratic":
        W = np.zeros((k, k))
        denom = (k - 1) ** 2 if k > 1 else 1
        for i in range(k):
            for j in range(k):
                W[i, j] = ((i - j) ** 2) / denom
        num = (W * O).sum()
        den = (W * E).sum()
        if den == 0:
            return np.nan
        return 1 - num / den
    po = np.trace(O)
    pe = np.trace(E)
    if np.isclose(pe, 1.0):
        return np.nan  # no disagreement possible: kappa undefined
    return (po - pe) / (1 - pe)


def interpret(k):
    """Landis-Koch bands, for the paper's prose."""
    if not np.isfinite(k):
        return "undefined"
    if k < 0:
        return "worse than chance"
    if k < 0.21:
        return "slight"
    if k < 0.41:
        return "fair"
    if k < 0.61:
        return "moderate"
    if k < 0.81:
        return "substantial"
    return "almost perfect"


# ------------------------------------------------------------------
# Data assembly
# ------------------------------------------------------------------

def judge_index():
    """{(dataset, model, technique, language): {item_id: score_dict}}"""
    out = {}
    for info, md, scores in C.iter_judge():
        key = (info["dataset"], info["model"], info["technique"],
               info["language"])
        out[key] = {s["id"]: s for s in scores}
    return out


def build_pairs():
    """Tidy table: one row per (item, criterion) with judge and human scores."""
    ji = judge_index()
    rows = []
    for info, reviews in C.iter_reviews():
        key = (info["dataset"], info["model"], info["technique"],
               info["language"])
        jscores = ji.get(key, {})
        for item_id, rev in reviews.items():
            j = jscores.get(item_id)
            for crit in CRITERIA:
                hv = rev.get(crit)
                if hv is None:
                    continue
                rows.append({
                    "dataset": info["dataset"],
                    "model": info["model"],
                    "technique": info["technique"],
                    "language": info["language"],
                    "reviewer": info["reviewer"],
                    "id": item_id,
                    "criterion": crit,
                    "human": int(hv),
                    "judge": (int(j[crit]) if j is not None
                              and j.get(crit) is not None else np.nan),
                    "judge_available": j is not None,
                })
    return pd.DataFrame(rows)


def build_kappa(pairs):
    """Judge-vs-human and human-vs-human kappa per criterion."""
    rows = []

    # ---- judge vs human, pooled over reviewers ----
    jh = pairs[pairs.judge_available & pairs.judge.notna()]
    for crit in CRITERIA:
        s = jh[jh.criterion == crit]
        if s.empty:
            continue
        cats = SCALE[crit]
        rows.append(_kappa_row("judge_vs_human", "pooled", crit, s.human,
                               s.judge, cats))

    # ---- judge vs each reviewer ----
    for rev, g in jh.groupby("reviewer"):
        for crit in CRITERIA:
            s = g[g.criterion == crit]
            if s.empty:
                continue
            rows.append(_kappa_row("judge_vs_human", rev, crit, s.human,
                                   s.judge, SCALE[crit]))

    # ---- human vs human, on items two reviewers both scored ----
    keyc = ["dataset", "model", "technique", "language", "id", "criterion"]
    for (rev_a, rev_b) in combinations(sorted(pairs.reviewer.unique()), 2):
        a = pairs[pairs.reviewer == rev_a].set_index(keyc)["human"]
        b = pairs[pairs.reviewer == rev_b].set_index(keyc)["human"]
        common = a.index.intersection(b.index)
        if len(common) == 0:
            continue
        for crit in CRITERIA:
            sel = [c for c in common if c[-1] == crit]
            if not sel:
                continue
            rows.append(_kappa_row("human_vs_human", f"{rev_a}|{rev_b}", crit,
                                   a.loc[sel], b.loc[sel], SCALE[crit]))
    return pd.DataFrame(rows)


def _kappa_row(comparison, who, crit, x, y, cats):
    """Agreement statistics for one paired sample.

    Reports kappa alongside the marginal statistics needed to read it.
    Cohen's kappa collapses toward 0 when the two raters have very
    different marginal distributions even while raw agreement is high
    (the "kappa paradox"). `bias_index` and `severity_gap` expose that
    directly, and PABAK gives a prevalence-and-bias-adjusted alternative,
    so a low kappa can be attributed either to noise or to a systematic
    severity difference.
    """
    x = np.asarray(x, dtype=float)
    y = np.asarray(y, dtype=float)
    ok = np.isfinite(x) & np.isfinite(y)
    x, y = x[ok].astype(int), y[ok].astype(int)
    kn = cohen_kappa(x, y, cats)
    kq = cohen_kappa(x, y, cats, weights="quadratic")
    n = len(x)
    po = float((x == y).mean()) if n else np.nan
    # share of each rater's scores at the top of the scale
    top = max(cats)
    p_top_first = float((x == top).mean()) if n else np.nan
    p_top_second = float((y == top).mean()) if n else np.nan
    # PABAK for the ordinal scale, using exact-match agreement
    k_cats = len(cats)
    pabak = ((k_cats * po) - 1) / (k_cats - 1) if n and k_cats > 1 else np.nan
    # signed disagreement: >0 means the first rater scores higher
    signed = float((x - y).mean()) if n else np.nan
    return {
        "comparison": comparison,
        "who": who,
        "criterion": crit,
        "n_items": n,
        "raw_agreement": po,
        "cohen_kappa": kn,
        "quadratic_weighted_kappa": kq,
        "pabak": pabak,
        "mean_abs_diff": float(np.abs(x - y).mean()) if n else np.nan,
        "severity_gap": signed,
        "bias_index": abs(p_top_first - p_top_second),
        "share_top_first": p_top_first,
        "share_top_second": p_top_second,
        "mean_first": float(x.mean()) if n else np.nan,
        "mean_second": float(y.mean()) if n else np.nan,
        "interpretation_nominal": interpret(kn),
    }


def build_kappa_by_file(pairs):
    rows = []
    grp = ["dataset", "model", "technique", "language", "reviewer"]
    for keys, g in pairs.groupby(grp):
        for crit in CRITERIA:
            s = g[(g.criterion == crit) & g.judge.notna()]
            if s.empty:
                continue
            r = _kappa_row("judge_vs_human", keys[-1], crit, s.human, s.judge,
                           SCALE[crit])
            r.update(dict(zip(grp, keys)))
            rows.append(r)
    return pd.DataFrame(rows)


def build_human_overlap(pairs):
    """Files scored by more than one reviewer."""
    grp = ["dataset", "model", "technique", "language"]
    rows = []
    for keys, g in pairs.groupby(grp):
        revs = sorted(g.reviewer.unique())
        n_shared = 0
        if len(revs) > 1:
            sets = [set(g[g.reviewer == r].id) for r in revs]
            n_shared = len(set.intersection(*sets))
        rows.append(dict(zip(grp, keys), n_reviewers=len(revs),
                         reviewers="|".join(revs),
                         n_items=g.id.nunique(),
                         n_shared_items=n_shared))
    return pd.DataFrame(rows)


# ------------------------------------------------------------------
# Figures
# ------------------------------------------------------------------

def fig_kappa(kappa):
    """Judge-vs-human against human-vs-human, per criterion."""
    jh = kappa[(kappa.comparison == "judge_vs_human") & (kappa.who == "pooled")]
    hh = kappa[kappa.comparison == "human_vs_human"]
    fig, ax = plt.subplots(figsize=(5.2, 3.1))
    x = np.arange(len(CRITERIA))
    w = 0.36
    jv = [float(jh[jh.criterion == c].quadratic_weighted_kappa.mean())
          if (jh.criterion == c).any() else np.nan for c in CRITERIA]
    hv = [float(hh[hh.criterion == c].quadratic_weighted_kappa.mean())
          if (hh.criterion == c).any() else np.nan for c in CRITERIA]
    ax.bar(x - w / 2, jv, width=w, color=FOCAL, label="judge vs human",
           edgecolor="white", linewidth=0.4)
    ax.bar(x + w / 2, hv, width=w, color=COMPARATOR, label="human vs human",
           edgecolor="white", linewidth=0.4)
    for xi, v in zip(x - w / 2, jv):
        if np.isfinite(v):
            ax.text(xi, v + 0.015, f"{v:.2f}", ha="center", fontsize=6)
    for xi, v in zip(x + w / 2, hv):
        if np.isfinite(v):
            ax.text(xi, v + 0.015, f"{v:.2f}", ha="center", fontsize=6)
    ax.axhline(0, color="0.3", lw=0.8)
    ax.set_xticks(x)
    ax.set_xticklabels([c.replace("_", " ") for c in CRITERIA])
    ax.set_ylabel("quadratic weighted kappa")
    ax.set_title("Judge-human agreement, against the human-human ceiling")
    ax.legend(frameon=False, loc="upper right")
    ax.margins(y=0.16)
    return fig


def fig_judge_vs_human_scatter(pairs):
    """Score distribution: how the judge and the humans differ per criterion."""
    jh = pairs[pairs.judge.notna()]
    fig, axes = plt.subplots(1, len(CRITERIA), figsize=(6.4, 2.4))
    for ax, crit in zip(np.atleast_1d(axes), CRITERIA):
        s = jh[jh.criterion == crit]
        cats = SCALE[crit]
        m = np.zeros((len(cats), len(cats)))
        for h, j in zip(s.human, s.judge):
            if h in cats and j in cats:
                m[cats.index(int(h)), cats.index(int(j))] += 1
        tot = m.sum()
        im = ax.imshow(m / tot if tot else m, cmap="viridis", vmin=0, vmax=0.6,
                       aspect="auto")
        ax.set_xticks(range(len(cats)))
        ax.set_xticklabels(cats, fontsize=6)
        ax.set_yticks(range(len(cats)))
        ax.set_yticklabels(cats, fontsize=6)
        ax.set_xlabel("judge")
        if crit == CRITERIA[0]:
            ax.set_ylabel("human")
        ax.set_title(crit.replace("_", " "), fontsize=7)
        for i in range(len(cats)):
            for j in range(len(cats)):
                if tot:
                    v = m[i, j] / tot
                    ax.text(j, i, f"{v:.2f}", ha="center", va="center",
                            fontsize=5.5,
                            color="white" if v < 0.3 else "black")
        ax.grid(False)
    fig.suptitle("Human vs judge score pairs (cell = share of compared items)",
                 fontsize=8)
    fig.tight_layout()
    return fig


# ------------------------------------------------------------------

def main():
    C.ensure_dirs()
    print("Judge-human agreement")

    pairs = build_pairs()
    C.save_table(pairs, "agreement_by_item.csv")

    kappa = build_kappa(pairs)
    C.save_table(kappa, "kappa.csv")

    byfile = build_kappa_by_file(pairs)
    C.save_table(byfile, "kappa_by_file.csv")

    overlap = build_human_overlap(pairs)
    C.save_table(overlap, "human_overlap.csv")

    C.save_fig(fig_kappa(kappa), "kappa_by_criterion.png")
    C.save_fig(fig_judge_vs_human_scatter(pairs), "judge_vs_human_scatter.png")

    n_rev_items = pairs.groupby(["reviewer"]).id.nunique().to_dict()
    print(f"\n  review files: {len(C.review_files())}")
    print(f"  reviewed items per reviewer: {n_rev_items}")
    print(f"  paired (item, criterion) rows: {len(pairs)}")
    print("  judge-comparable rows: "
          f"{int(pairs.judge.notna().sum())}")
    print(f"  files with 2 reviewers: {int((overlap.n_reviewers > 1).sum())}")
    print("\n  kappa (quadratic weighted):")
    for _, r in kappa[(kappa.comparison == "judge_vs_human")
                      & (kappa.who == "pooled")].iterrows():
        print(f"    judge-human {r.criterion:15s} n={r.n_items:4d} "
              f"kw={r.quadratic_weighted_kappa:.3f} "
              f"nominal={r.cohen_kappa:.3f} ({r.interpretation_nominal})")
    for _, r in kappa[kappa.comparison == "human_vs_human"].iterrows():
        print(f"    human-human {r.criterion:15s} n={r.n_items:4d} "
              f"kw={r.quadratic_weighted_kappa:.3f} "
              f"nominal={r.cohen_kappa:.3f} ({r.interpretation_nominal})")
    return pairs


if __name__ == "__main__":
    main()
