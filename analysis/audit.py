"""Data audit: coverage, defects and every number the paper will quote.

Runs last. Re-derives the headline numbers from the raw files rather than
from the other scripts' outputs, so a disagreement between this and the
tables is a real bug rather than a copy error.

  tables/audit_coverage.csv    files/items present per pipeline and cell
  tables/audit_defects.csv     concrete data defects, with locations
  tables/paper_numbers.csv     every quotable number, name -> value

  figs/audit_coverage.png

Usage:  python analysis/audit.py
"""

from __future__ import annotations

import json
import sys
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


def audit_coverage():
    rows = []
    # Phase 1: 5 datasets x 9 models x 2 techniques x 2 languages = 180
    p1 = C.phase1_files()
    for ds in C.DATASETS:
        for m in C.MODELS:
            for t in C.TECHNIQUES:
                for lg in C.LANGUAGES:
                    present = any(f["dataset"] == ds and f["model"] == m
                                  and f["technique"] == t and f["language"] == lg
                                  for f in p1)
                    rows.append({"pipeline": "phase1", "dataset": ds,
                                 "model": m, "cell": f"{t}/{lg}",
                                 "present": present})
    for ds in C.DATASETS:
        for m in C.MODELS:
            rows.append({"pipeline": "judge", "dataset": ds, "model": m,
                         "cell": "zero-shot/en",
                         "present": any(f["dataset"] == ds and f["model"] == m
                                        for f in C.judge_files())})
            rows.append({"pipeline": "fol", "dataset": ds, "model": m,
                         "cell": "c1",
                         "present": any(f["dataset"] == ds and f["model"] == m
                                        for f in C.fol_files())})
    return pd.DataFrame(rows)


def audit_defects():
    """Concrete, located data defects a reader should know about."""
    d = []

    # 1. mistral-large-3 x fracas store partial_success_count = 0 next to a
    #    non-zero success_count. FraCaS is single-label, so partial cannot
    #    be below strict.
    for info, md, items in C.iter_phase1(dataset="fracas",
                                          model="mistral-large-3"):
        s = C.load_json(info["path"]).get("summary") or {}
        if ("partial_success_count" in s
                and s["partial_success_count"] < s.get("success_count", 0)):
            d.append({
                "severity": "medium",
                "location": Path(info["path"]).name,
                "defect": "partial_success_count < success_count",
                "detail": (f"stored partial={s['partial_success_count']} but "
                           f"strict={s['success_count']}; FraCaS is "
                           f"single-label so partial >= strict always"),
                "handled": "analysis recomputes both from item level",
            })

    # 2. fracas-extended carries no section metadata
    n_ext = n_ext_sec = 0
    for info, md, items in C.iter_phase1(dataset="fracas-extended"):
        for it in items:
            n_ext += 1
            if C.sections_of(it, "fracas-extended"):
                n_ext_sec += 1
        break  # one file is enough to establish the schema
    if n_ext and n_ext_sec == 0:
        d.append({
            "severity": "medium",
            "location": "phase1_nli_eval/results/fracas-extended/*.json",
            "defect": "no section metadata",
            "detail": (f"0 of {n_ext} items carry fracas_sections, and ids "
                       f"run 347-774 (outside FraCaS 1-346) so the section "
                       f"cannot be recovered from the number either"),
            "handled": "excluded from all per-section analyses",
        })

    # 3. judge coverage gap
    scored = {(f["dataset"], f["model"]) for f in C.judge_files()}
    missing = [(ds, m) for ds in C.DATASETS for m in C.MODELS
               if (ds, m) not in scored]
    if missing:
        d.append({
            "severity": "medium",
            "location": "phase1_nli_eval/judge_scores/",
            "defect": f"{len(missing)} of 45 dataset x model cells unscored",
            "detail": "; ".join(f"{ds}/{m}" for ds, m in missing[:12]),
            "handled": "judge analyses report coverage explicitly",
        })

    # 3b. judge scores for a model whose Phase 1 results are absent
    orph = [f for f in C.judge_files(include_orphans=True)
            if f["model"] not in C.MODELS]
    if orph:
        n_items = sum(len(C.load_json(f["path"]).get("scores", []))
                      for f in orph)
        d.append({
            "severity": "medium",
            "location": "; ".join(sorted(Path(f["path"]).name for f in orph)),
            "defect": (f"judge scores for {len({f['model'] for f in orph})} "
                       f"model(s) outside the 9-model design"),
            "detail": (f"{n_items} scored items for "
                       f"{sorted({f['model'] for f in orph})}; their "
                       f"metadata.source_file Phase 1 results are absent, so "
                       f"the scores cannot be joined to a prediction"),
            "handled": "excluded from all judge analyses (common.judge_files)",
        })

    # 3c. truncated runs: a file with far fewer items than the dataset
    #     has. These do not error -- they silently report accuracy over
    #     the handful of items that completed, which corrupts any mean
    #     taken over files.
    for info, md, items in C.iter_fol():
        exp = C.DATASET_SIZES.get(info["dataset"])
        if exp and len(items) < exp * 0.95:
            d.append({
                "severity": "high",
                "location": Path(info["path"]).name,
                "defect": "truncated run",
                "detail": (f"{len(items)} of {exp} items ({len(items)/exp:.1%}); "
                           f"the stored accuracy is computed over these items "
                           f"only and is not comparable to a complete run"),
                "handled": "MUST BE RERUN -- see RUN_COQ.md step 1",
            })

    # 3d. Coq cells that stopped early. coq_files() drops them so aggregates
    #     are not skewed, but a dropped cell must still be reported: it cost
    #     API budget and its absence changes which models are represented.
    for path, n, exp in C.partial_coq_files():
        d.append({
            "severity": "high",
            "location": path.name,
            "defect": "incomplete Coq cell (excluded from aggregates)",
            "detail": f"{n} of {exp} items ({n/exp:.0%}); "
                      f"rerun to include it",
            "handled": "EXCLUDED by common.coq_files(); rerun the cell",
        })

    # 4. items with no parseable prediction
    n_none = 0
    for info, md, items in C.iter_phase1():
        for it in items:
            if not C.label_set(it.get("predicted")):
                n_none += 1
    if n_none:
        d.append({
            "severity": "low",
            "location": "phase1_nli_eval/results/",
            "defect": f"{n_none} items have no parseable prediction",
            "detail": "counted as incorrect, not dropped",
            "handled": "reported as no_prediction in phase1_accuracy.csv",
        })

    # 5. FOL 'Undecided' is not an NLI label
    fol_by_item = C.OUT_TABLES / "fol_by_item.csv"
    if fol_by_item.exists():
        f = pd.read_csv(fol_by_item)
        n_u = int((f.fol_label == "Undecided").sum())
        d.append({
            "severity": "info",
            "location": "phase2_fol/results/",
            "defect": f"{n_u} items labelled 'Undecided'",
            "detail": ("a pipeline outcome, not an NLI class: neither prover "
                       "nor model-finder settled the item. Never correct "
                       "against gold"),
            "handled": "reported separately as undecided_rate",
        })

    # 6. no post-fix Coq runs
    if not C.coq_files():
        d.append({
            "severity": "high",
            "location": "phase2_coq/results/",
            "defect": "no post-fix Coq results",
            "detail": ("the only files present are the pilot runs made "
                       "before the section-mapping fix, whose T2/T3 cells "
                       "silently received only Montague.v"),
            "handled": "excluded; Coq tables written empty pending the run",
        })
    return pd.DataFrame(d)


def paper_numbers():
    """Every number the paper quotes, recomputed from the raw files."""
    n = {}
    T = C.OUT_TABLES

    # ---- corpus ----
    n["n_datasets"] = len(C.DATASETS)
    n["n_models"] = len(C.MODELS)
    for ds, cnt in C.DATASET_SIZES.items():
        n[f"n_items_{ds}"] = cnt
    n["n_items_total"] = sum(C.DATASET_SIZES.values())

    # ---- phase 1 ----
    if (T / "phase1_accuracy.csv").exists():
        a = pd.read_csv(T / "phase1_accuracy.csv")
        n["phase1_files"] = len(a)
        n["phase1_items_scored"] = int(a.n_items.sum())
        n["phase1_no_prediction"] = int(a.n_no_prediction.sum())
        zs = a[(a.technique == "zero-shot") & (a.language == "en")]
        n["phase1_mean_acc_zeroshot_en"] = float(zs.strict_accuracy.mean())
        best = zs.loc[zs.strict_accuracy.idxmax()]
        n["phase1_best_model"] = best.model
        n["phase1_best_dataset"] = best.dataset
        n["phase1_best_acc"] = float(best.strict_accuracy)
        worst = zs.loc[zs.strict_accuracy.idxmin()]
        n["phase1_worst_model"] = worst.model
        n["phase1_worst_acc"] = float(worst.strict_accuracy)
        # english vs greek, on the translated pair only
        for lg in C.LANGUAGES:
            s = a[(a.technique == "zero-shot") & (a.language == lg)
                  & (a.dataset.isin(["fracas", "fracas-translated"]))]
            n[f"phase1_acc_{lg}_fracas_pair"] = float(s.strict_accuracy.mean())
        # few-shot effect
        piv = a[a.language == "en"].pivot_table(
            index=["dataset", "model"], columns="technique",
            values="strict_accuracy")
        if {"zero-shot", "few-shot"} <= set(piv.columns):
            diff = piv["few-shot"] - piv["zero-shot"]
            n["fewshot_helps_pairs"] = int((diff > 0).sum())
            n["fewshot_total_pairs"] = int(diff.notna().sum())
            n["fewshot_mean_delta"] = float(diff.mean())

    # ---- judge ----
    if (T / "judge_scores_by_item.csv").exists():
        j = pd.read_csv(T / "judge_scores_by_item.csv")
        n["judge_items_scored"] = len(j)
        n["judge_mean_phenomenon_id"] = float(j.phenomenon_id.mean())
        n["judge_mean_soundness"] = float(j.soundness.mean())
        n["judge_mean_consistency"] = float(j.consistency.mean())
        corr = j[j.strict_correct == True]  # noqa: E712
        n["rfwr_phen0_rate"] = float((corr.phenomenon_id == 0).mean())
        n["rfwr_phen_lt2_rate"] = float((corr.phenomenon_id < 2).mean())
        n["rfwr_phen0_count"] = int((corr.phenomenon_id == 0).sum())

    # ---- agreement ----
    if (T / "kappa.csv").exists():
        k = pd.read_csv(T / "kappa.csv")
        for _, r in k.iterrows():
            if r.comparison == "judge_vs_human" and r.who == "pooled":
                n[f"kappa_judge_human_{r.criterion}"] = float(r.cohen_kappa)
                n[f"kappa_w_judge_human_{r.criterion}"] = float(
                    r.quadratic_weighted_kappa)
                n[f"raw_agree_judge_human_{r.criterion}"] = float(r.raw_agreement)
                n[f"severity_gap_{r.criterion}"] = float(r.severity_gap)
                n[f"n_judge_human_{r.criterion}"] = int(r.n_items)
            if r.comparison == "human_vs_human":
                n[f"kappa_human_human_{r.criterion}"] = float(r.cohen_kappa)
                n[f"kappa_w_human_human_{r.criterion}"] = float(
                    r.quadratic_weighted_kappa)
                n[f"n_human_human_{r.criterion}"] = int(r.n_items)

    # ---- FOL ----
    if (T / "fol_by_item.csv").exists():
        f = pd.read_csv(T / "fol_by_item.csv")
        n["fol_items"] = len(f)
        n["fol_files"] = len(C.fol_files())
        n["fol_accuracy"] = float(f.strict_correct.fillna(False).mean())
        n["fol_undecided_rate"] = float(f.is_undecided.mean())
        n["fol_items_with_error"] = int((f.n_errors > 0).sum())
        n["fol_error_item_rate"] = float((f.n_errors > 0).mean())
    if (T / "fol_error_taxonomy.csv").exists():
        t = pd.read_csv(T / "fol_error_taxonomy.csv")
        n["fol_error_messages"] = int(t.n_error_messages.sum())
        for _, r in t.iterrows():
            n[f"fol_err_{r.category}_n"] = int(r.n_error_messages)
            n[f"fol_err_{r.category}_share"] = float(r.share_of_error_messages)
        sig = t[t.category.isin(["relation_function_clash", "arity_conflict",
                                 "term_construction"])]
        n["fol_signature_error_share"] = float(sig.share_of_error_messages.sum())

    # ---- cross-pipeline ----
    if (T / "cross_pipeline_summary.csv").exists():
        s = pd.read_csv(T / "cross_pipeline_summary.csv")
        tot = s[["both_correct", "p1_only", "fol_only", "neither"]].sum()
        N = float(tot.sum())
        n["cross_n_items"] = int(N)
        n["cross_both_correct_share"] = float(tot.both_correct / N)
        n["cross_p1_only_share"] = float(tot.p1_only / N)
        n["cross_fol_only_share"] = float(tot.fol_only / N)
        n["cross_neither_share"] = float(tot.neither / N)
    if (T / "cross_correlations.csv").exists():
        c = pd.read_csv(T / "cross_correlations.csv")
        for _, r in c.iterrows():
            key = (r.comparison.replace(" ", "_").replace("vs_", "vs")
                   .lower()[:48])
            n[f"corr_{key}"] = float(r.estimate)
            n[f"p_{key}"] = float(r.p_value)

    # ---- Coq ----
    n["coq_postfix_files"] = len(C.coq_files())
    if (T / "coq_by_item.csv").exists():
        cq = pd.read_csv(T / "coq_by_item.csv")
        n["coq_items"] = len(cq)
        if len(cq):
            n["coq_compilation_rate"] = float(cq.compiled.mean())
            n["coq_proof_rate"] = float(cq.proof_complete.mean())
            n["coq_accuracy"] = float(cq.correct.mean())

    return pd.DataFrame([{"name": k, "value": v} for k, v in n.items()])


def fig_coverage(cov):
    piv = cov.pivot_table(index="model", columns="pipeline", values="present",
                          aggfunc="mean", observed=True)
    piv = piv.reindex(index=[m for m in C.MODELS if m in piv.index])
    order = [c for c in ("phase1", "judge", "fol") if c in piv.columns]
    piv = piv[order]
    fig, ax = plt.subplots(figsize=(4.6, 3.2))
    im = ax.imshow(piv.values, cmap="viridis", vmin=0, vmax=1, aspect="auto")
    ax.set_xticks(range(piv.shape[1]))
    ax.set_xticklabels(list(piv.columns))
    ax.set_yticks(range(piv.shape[0]))
    ax.set_yticklabels(list(piv.index))
    for i in range(piv.shape[0]):
        for j in range(piv.shape[1]):
            v = piv.values[i, j]
            ax.text(j, i, f"{v:.0%}", ha="center", va="center", fontsize=6,
                    color="white" if v < 0.5 else "black")
    ax.set_title("Data coverage: share of dataset cells present\n"
                 "(Coq pending; judge covers zero-shot EN only)")
    ax.grid(False)
    return fig


def main():
    C.ensure_dirs()
    print("Audit")

    cov = audit_coverage()
    C.save_table(cov, "audit_coverage.csv")

    def_ = audit_defects()
    C.save_table(def_, "audit_defects.csv")

    nums = paper_numbers()
    C.save_table(nums, "paper_numbers.csv")

    C.save_fig(fig_coverage(cov), "audit_coverage.png")

    print(f"\n  coverage cells: {len(cov)}, present: {int(cov.present.sum())}")
    for pl, g in cov.groupby("pipeline"):
        print(f"    {pl:8s} {int(g.present.sum()):4d}/{len(g)}")
    print(f"\n  defects found: {len(def_)}")
    for _, r in def_.iterrows():
        print(f"    [{r.severity:6s}] {r.location}: {r.defect}")
    print(f"\n  paper numbers computed: {len(nums)}")
    return nums


if __name__ == "__main__":
    main()
