"""
NESTOR Phase 3 — Comparison & Analysis
=======================================
Builds the 2x2 matrix (FOL success/fail × Coq success/fail) per phenomenon.
Compares LLM-only vs FOL+Prover vs Coq across all items.

Usage:
  python compare.py --fol results/fol_gpt4o.json --coq results/coq_gpt4o.json --phase1 results/phase1_gpt4o.json
"""

import json
import argparse
from collections import defaultdict

def load_results(path):
    with open(path) as f:
        return {r["id"]: r for r in json.load(f)}


def build_2x2_matrix(fol_results, coq_results):
    """Build FOL×Coq success matrix."""
    matrix = {"both_success": [], "fol_only": [], "coq_only": [], "both_fail": []}

    all_ids = set(fol_results.keys()) & set(coq_results.keys())

    for pid in sorted(all_ids):
        fol_ok = fol_results[pid].get("proved", False) or fol_results[pid].get("countermodel", False)
        coq_ok = coq_results[pid].get("proof_complete", False)

        if fol_ok and coq_ok:
            matrix["both_success"].append(pid)
        elif fol_ok and not coq_ok:
            matrix["fol_only"].append(pid)
        elif not fol_ok and coq_ok:
            matrix["coq_only"].append(pid)
        else:
            matrix["both_fail"].append(pid)

    return matrix


def print_matrix(matrix, total):
    print("\n=== 2×2 Matrix: FOL × Coq ===\n")
    print(f"                  Coq success    Coq fail")
    print(f"  FOL success     {len(matrix['both_success']):>5}          {len(matrix['fol_only']):>5}")
    print(f"  FOL fail        {len(matrix['coq_only']):>5}          {len(matrix['both_fail']):>5}")
    print(f"\n  Total items: {total}")
    print(f"  Both succeed: {len(matrix['both_success'])} ({len(matrix['both_success'])/total:.1%})")
    print(f"  FOL only:     {len(matrix['fol_only'])} ({len(matrix['fol_only'])/total:.1%})")
    print(f"  Coq only:     {len(matrix['coq_only'])} ({len(matrix['coq_only'])/total:.1%})")
    print(f"  Both fail:    {len(matrix['both_fail'])} ({len(matrix['both_fail'])/total:.1%})")


def three_way_comparison(phase1, fol_results, coq_results):
    """Compare LLM-only vs FOL vs Coq accuracy."""
    all_ids = set(phase1.keys()) & set(fol_results.keys()) & set(coq_results.keys())

    llm_correct = 0
    fol_correct = 0
    coq_correct = 0

    for pid in all_ids:
        gold = phase1[pid].get("gold", "")

        # LLM-only
        if phase1[pid].get("correct", False):
            llm_correct += 1

        # FOL
        if fol_results[pid].get("correct", False):
            fol_correct += 1

        # Coq — check if proof_complete matches gold
        coq_ok = coq_results[pid].get("proof_complete", False)
        if coq_ok and gold in ("yes", "entailment"):
            coq_correct += 1
        elif not coq_ok and gold in ("no", "unknown", "contradiction", "neutral"):
            coq_correct += 1

    total = len(all_ids)
    print(f"\n=== Three-Way Accuracy Comparison ===\n")
    print(f"  LLM-only:   {llm_correct}/{total} ({llm_correct/total:.1%})")
    print(f"  FOL+Prover: {fol_correct}/{total} ({fol_correct/total:.1%})")
    print(f"  Coq:        {coq_correct}/{total} ({coq_correct/total:.1%})")


def loop_analysis(results, label=""):
    """Analyze verification loop effectiveness."""
    total = len(results)
    first_pass = sum(1 for r in results.values() if r.get("attempts", 99) == 1
                     and (r.get("proved") or r.get("proof_complete")))
    eventually = sum(1 for r in results.values()
                     if r.get("proved") or r.get("countermodel") or r.get("proof_complete"))
    loop_gain = eventually - first_pass

    print(f"\n=== Loop Analysis ({label}) ===\n")
    print(f"  Total items:       {total}")
    print(f"  First-pass success: {first_pass} ({first_pass/total:.1%})")
    print(f"  Eventually success: {eventually} ({eventually/total:.1%})")
    print(f"  Loop gain:         +{loop_gain} ({loop_gain/total:.1%})")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--fol", required=True, help="FOL results JSON")
    parser.add_argument("--coq", required=True, help="Coq results JSON")
    parser.add_argument("--phase1", default=None, help="Phase 1 results JSON")
    args = parser.parse_args()

    fol = load_results(args.fol)
    coq = load_results(args.coq)

    matrix = build_2x2_matrix(fol, coq)
    total = len(set(fol.keys()) & set(coq.keys()))
    print_matrix(matrix, total)

    loop_analysis(fol, "FOL")
    loop_analysis(coq, "Coq")

    if args.phase1:
        phase1 = load_results(args.phase1)
        three_way_comparison(phase1, fol, coq)
