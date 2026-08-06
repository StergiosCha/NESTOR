"""Phase 1 NLI accuracy: tables, confusion matrices, section breakdown.

Reads every well-formed file under phase1_nli_eval/results/ (180 files =
5 datasets x 9 models x 2 techniques x 2 languages) and writes:

  tables/phase1_accuracy.csv       one row per file: strict + partial accuracy
  tables/phase1_accuracy_wide.csv  model x dataset (zero-shot, en) matrix
  tables/phase1_confusion.csv      pooled gold x predicted counts per dataset
  tables/phase1_by_section.csv     accuracy per FraCaS section x model
  tables/phase1_conditions.csv     technique and language contrasts per model

  figs/phase1_accuracy_heatmap.png
  figs/zeroshot_vs_fewshot.png
  figs/en_vs_el.png
  figs/phase1_by_section.png

Usage:  python analysis/phase1_tables.py
"""

from __future__ import annotations

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
    apply_figure_style()  # noqa: F821  (kernel plugin, when present)
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


# ------------------------------------------------------------------
# 1. Per-file accuracy
# ------------------------------------------------------------------

def build_accuracy():
    rows = []
    for info, md, items in C.iter_phase1():
        n = len(items)
        strict = partial = 0
        no_pred = 0
        for it in items:
            s, p = C.correctness(it.get("predicted"), it.get("gold"))
            if s is None:
                no_pred += 1
                continue
            strict += bool(s)
            partial += bool(p)
        rows.append({
            "dataset": info["dataset"],
            "model": info["model"],
            "technique": info["technique"],
            "language": info["language"],
            "n_items": n,
            "n_no_prediction": no_pred,
            "n_strict_correct": strict,
            "n_partial_correct": partial,
            "strict_accuracy": strict / n if n else np.nan,
            "partial_accuracy": partial / n if n else np.nan,
            "crosslingual": bool(md.get("crosslingual", False)),
            "multilabel": bool(md.get("multilabel", False)),
        })
    df = pd.DataFrame(rows)
    df["dataset"] = pd.Categorical(df["dataset"], C.DATASETS, ordered=True)
    df["model"] = pd.Categorical(df["model"], C.MODELS, ordered=True)
    return df.sort_values(["dataset", "model", "technique", "language"])


# ------------------------------------------------------------------
# 2. Confusion matrices
# ------------------------------------------------------------------

def build_confusion():
    """Pooled gold x predicted counts per dataset (zero-shot, en).

    Multi-label gold/prediction sets are reduced to a single label when
    unambiguous; ambiguous rows are counted in the `multi` bucket so no
    item is silently dropped.
    """
    rows = []
    for ds in C.DATASETS:
        counts = Counter()
        multi = 0
        for info, md, items in C.iter_phase1(dataset=ds, technique="zero-shot",
                                             language="en"):
            for it in items:
                g = C.primary(it.get("gold"))
                p = C.primary(it.get("predicted"))
                if g is None or p is None:
                    multi += 1
                    continue
                counts[(g, p)] += 1
        for g in C.LABELS:
            row = {"dataset": ds, "gold": g}
            total = sum(counts[(g, p)] for p in C.LABELS)
            for p in C.LABELS:
                row[f"pred_{p}"] = counts[(g, p)]
                row[f"frac_{p}"] = counts[(g, p)] / total if total else np.nan
            row["gold_total"] = total
            rows.append(row)
        rows.append({"dataset": ds, "gold": "AMBIGUOUS_OR_MISSING",
                     "gold_total": multi})
    return pd.DataFrame(rows)


# ------------------------------------------------------------------
# 3. Section breakdown
# ------------------------------------------------------------------

def build_by_section():
    """Accuracy per FraCaS section, per model, zero-shot EN.

    Items with several section tags contribute to each of them, so
    section columns need not sum to the dataset total.
    """
    acc = defaultdict(lambda: [0, 0])
    for info, md, items in C.iter_phase1(technique="zero-shot", language="en"):
        for it in items:
            s, _ = C.correctness(it.get("predicted"), it.get("gold"))
            if s is None:
                continue
            for sec in C.sections_of(it, info["dataset"]):
                key = (info["dataset"], info["model"], sec)
                acc[key][0] += bool(s)
                acc[key][1] += 1
    rows = [{
        "dataset": ds, "model": m, "section": sec,
        "section_name": C.SECTION_NAME.get(sec, "?"),
        "n_correct": k, "n_items": n,
        "accuracy": k / n if n else np.nan,
    } for (ds, m, sec), (k, n) in sorted(acc.items(), key=lambda kv: (str(kv[0][0]), str(kv[0][1]), kv[0][2]))]
    return pd.DataFrame(rows)


# ------------------------------------------------------------------
# 4. Condition contrasts
# ------------------------------------------------------------------

def build_conditions(acc):
    """Zero-shot vs few-shot, and EN vs EL, per model x dataset."""
    piv = acc.pivot_table(index=["dataset", "model"],
                          columns=["technique", "language"],
                          values="strict_accuracy", observed=True)
    rows = []
    for (ds, m), r in piv.iterrows():
        def g(t, l):
            try:
                return float(r[(t, l)])
            except (KeyError, TypeError):
                return np.nan
        rows.append({
            "dataset": ds, "model": m,
            "zero_shot_en": g("zero-shot", "en"),
            "few_shot_en": g("few-shot", "en"),
            "zero_shot_el": g("zero-shot", "el"),
            "few_shot_el": g("few-shot", "el"),
            "fewshot_gain_en": g("few-shot", "en") - g("zero-shot", "en"),
            "fewshot_gain_el": g("few-shot", "el") - g("zero-shot", "el"),
            "en_minus_el_zeroshot": g("zero-shot", "en") - g("zero-shot", "el"),
            "en_minus_el_fewshot": g("few-shot", "en") - g("few-shot", "el"),
        })
    return pd.DataFrame(rows)


# ------------------------------------------------------------------
# Figures
# ------------------------------------------------------------------

def fig_accuracy_heatmap(acc):
    sub = acc[(acc.technique == "zero-shot") & (acc.language == "en")]
    m = sub.pivot_table(index="model", columns="dataset",
                        values="strict_accuracy", observed=True)
    m = m.reindex(index=[x for x in C.MODELS if x in m.index],
                  columns=[d for d in C.DATASETS if d in m.columns])
    fig, ax = plt.subplots(figsize=(5.2, 3.4))
    # Span the observed range rather than [0,1]: all values sit in a narrow
    # band, and a full-range colourbar would waste most of the scale (S3.2).
    vmin = float(np.nanmin(m.values))
    vmax = float(np.nanmax(m.values))
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
    ax.set_title("Zero-shot English accuracy is far below the FraCaS ceiling")
    ax.grid(False)
    cb = fig.colorbar(im, ax=ax, fraction=0.035, pad=0.02)
    cb.set_label("strict accuracy (higher = better)", fontsize=6)
    cb.ax.tick_params(labelsize=6)
    return fig


def _paired_scatter(ax, x, y, labels, xlabel, ylabel, title):
    ax.scatter(x, y, s=26, color=FOCAL, zorder=3, edgecolor="white",
               linewidth=0.5)
    lo = float(np.nanmin(np.concatenate([x, y]))) - 0.03
    hi = float(np.nanmax(np.concatenate([x, y]))) + 0.03
    ax.plot([lo, hi], [lo, hi], color="0.55", lw=0.8, ls="--", zorder=1)
    ax.set_xlim(lo, hi)
    ax.set_ylim(lo, hi)
    ax.set_xlabel(xlabel)
    ax.set_ylabel(ylabel)
    ax.set_title(title)
    # Label the two extremes by signed distance from the diagonal, with a
    # leader line so the text can sit clear of the dense point cloud (S6.9).
    d = y - x
    if np.isfinite(d).any():
        hi_i, lo_i = int(np.nanargmax(d)), int(np.nanargmin(d))
        for idx, (dx, dy) in ((hi_i, (-58, 24)), (lo_i, (16, -26))):
            ax.annotate(
                labels[idx], (x[idx], y[idx]),
                textcoords="offset points", xytext=(dx, dy), fontsize=6,
                color="0.25",
                arrowprops=dict(arrowstyle="-", lw=0.5, color="0.55",
                                shrinkA=0.5, shrinkB=3))
    return ax


def fig_zeroshot_vs_fewshot(cond):
    fig, axes = plt.subplots(1, 2, figsize=(6.4, 3.1))
    for ax, lang in zip(axes, ["en", "el"]):
        s = cond.dropna(subset=[f"zero_shot_{lang}", f"few_shot_{lang}"])
        lab = [f"{C.DATASET_DISPLAY[d]}/{m}" for d, m in zip(s.dataset, s.model)]
        _paired_scatter(ax, s[f"zero_shot_{lang}"].to_numpy(),
                        s[f"few_shot_{lang}"].to_numpy(), lab,
                        "zero-shot accuracy", "few-shot accuracy",
                        f"{lang.upper()} prompts")
    n_up = int((cond["fewshot_gain_en"] > 0).sum())
    n_tot = int(cond["fewshot_gain_en"].notna().sum())
    fig.suptitle(f"Few-shot exemplars help in only {n_up} of {n_tot} "
                 "model-dataset pairs (English)", y=1.02)
    fig.tight_layout()
    return fig


def fig_en_vs_el(cond):
    """Cross-lingual gap, excluding the dataset whose text is English-only."""
    s = cond[cond.dataset != "fracas"].dropna(subset=["en_minus_el_zeroshot"])
    order = s.groupby("model", observed=True)["en_minus_el_zeroshot"].mean(
        ).sort_values()
    fig, ax = plt.subplots(figsize=(5.0, 3.0))
    for i, m in enumerate(order.index):
        vals = s[s.model == m]["en_minus_el_zeroshot"]
        ax.scatter(vals, [i] * len(vals), s=22, color=COMPARATOR, zorder=2,
                   edgecolor="white", linewidth=0.4)
        ax.scatter([order[m]], [i], marker="|", s=200, color=FOCAL, zorder=3)
    ax.axvline(0, color="0.3", lw=0.9)
    ax.set_yticks(range(len(order)))
    ax.set_yticklabels(list(order.index))
    ax.set_xlabel("accuracy(EN prompt) - accuracy(EL prompt)")
    ax.set_title("Prompt language shifts accuracy on Greek data\n"
                 "(dot = dataset, bar = model mean; >0 favours English)")
    ax.margins(0.06)
    return fig


def fig_by_section(sec):
    s = sec[sec.dataset == "fracas"]
    m = s.pivot_table(index="model", columns="section", values="accuracy",
                      observed=True)
    m = m.reindex(index=[x for x in C.MODELS if x in m.index])
    fig, ax = plt.subplots(figsize=(5.6, 3.4))
    im = ax.imshow(m.values, cmap="viridis", vmin=0.2, vmax=1.0, aspect="auto")
    ax.set_xticks(range(m.shape[1]))
    ax.set_xticklabels([C.SECTION_SHORT.get(c, c) for c in m.columns],
                       rotation=40, ha="right")
    ax.set_yticks(range(m.shape[0]))
    ax.set_yticklabels(list(m.index))
    for i in range(m.shape[0]):
        for j in range(m.shape[1]):
            v = m.values[i, j]
            if np.isfinite(v):
                ax.text(j, i, f"{v:.2f}", ha="center", va="center", fontsize=5.5,
                        color="white" if v < 0.72 else "black")
    ax.set_title("FraCaS accuracy by linguistic phenomenon (zero-shot, EN)")
    ax.grid(False)
    cb = fig.colorbar(im, ax=ax, fraction=0.035, pad=0.02)
    cb.set_label("strict accuracy", fontsize=6)
    cb.ax.tick_params(labelsize=6)
    return fig


# ------------------------------------------------------------------

def main():
    C.ensure_dirs()
    print("Phase 1 accuracy tables")

    acc = build_accuracy()
    C.save_table(acc, "phase1_accuracy.csv")

    wide = acc[(acc.technique == "zero-shot") & (acc.language == "en")].pivot_table(
        index="model", columns="dataset", values="strict_accuracy", observed=True)
    C.save_table(wide.reset_index(), "phase1_accuracy_wide.csv")

    conf = build_confusion()
    C.save_table(conf, "phase1_confusion.csv")

    sec = build_by_section()
    C.save_table(sec, "phase1_by_section.csv")

    cond = build_conditions(acc)
    C.save_table(cond, "phase1_conditions.csv")

    C.save_fig(fig_accuracy_heatmap(acc), "phase1_accuracy_heatmap.png")
    C.save_fig(fig_zeroshot_vs_fewshot(cond), "zeroshot_vs_fewshot.png")
    C.save_fig(fig_en_vs_el(cond), "en_vs_el.png")
    C.save_fig(fig_by_section(sec), "phase1_by_section.png")

    print(f"\n  files read: {len(acc)}")
    print(f"  items scored: {int(acc.n_items.sum())}")
    print(f"  items with no parseable prediction: {int(acc.n_no_prediction.sum())}")
    print("  mean strict accuracy (zero-shot EN): "
          f"{acc[(acc.technique=='zero-shot')&(acc.language=='en')].strict_accuracy.mean():.4f}")
    return acc


if __name__ == "__main__":
    main()
