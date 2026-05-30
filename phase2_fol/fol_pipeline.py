"""
NESTOR Phase 2 — FOL Pipeline
==============================
NL → FOL (via LLM) → Prover9/MACE4 → result

Pipeline:
1. LLM translates P, H into FOL (Prover9 syntax)
2. Syntax check (parse the FOL before sending to prover)
3. Prover9: try to prove P ⊢ H (entailment)
4. MACE4: try to find countermodel for P ∧ ¬H (non-entailment)
5. Result: proved / countermodel / timeout

Verification loop (Phase 3):
If syntax error or prover failure, feed error back to LLM, retry up to k=3.

Requirements:
  pip install openai
  Prover9/MACE4 binaries in PATH (or set PROVER9_PATH env var)
"""

import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from dotenv import load_dotenv

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from clients.azure import get_client, call_llm
from utils.fracas import load_flat

load_dotenv()

PROVER9_PATH = os.environ.get("PROVER9_PATH", "")
MACE4_PATH = os.environ.get("MACE4_PATH", "")
PROVER_TIMEOUT = int(os.environ.get("PROVER_TIMEOUT", "30") or 30)

MAX_RETRIES = int(os.environ.get("MAX_RETRIES", "3") or 3)
PROMPT_DIR = Path(__file__).parent / "prompts"

FOL_MAX_TOKENS = 500

# ============================================================
# PHASE 1 RESULTS (for C2/C4 conditions)
# ============================================================

PHASE1_RESULTS_PATH = Path(__file__).resolve().parent.parent / "phase1_nli_eval" / "results" / "fracas_results_azure.json"

_phase1_cache = None

def load_phase1_results():
    """Load Phase 1 predictions (cached)."""
    global _phase1_cache
    if _phase1_cache is None:
        if PHASE1_RESULTS_PATH.exists():
            with open(PHASE1_RESULTS_PATH, encoding="utf-8") as f:
                _phase1_cache = json.load(f)
        else:
            print(f"WARNING: Phase 1 results not found at {PHASE1_RESULTS_PATH}")
            _phase1_cache = {}
    return _phase1_cache


def get_phase1_prediction(item_id, model="gpt-4o"):
    """Get Phase 1 prediction and explanation for an item."""
    results = load_phase1_results()
    # fracas_results_azure.json is keyed by model -> item_number
    item_num = item_id.split("-")[-1] if "-" in str(item_id) else str(item_id)
    model_results = results.get(model, {})
    entry = model_results.get(item_num, {})
    return {
        "label": entry.get("predicted", "unknown"),
        "explanation": entry.get("explanation", ""),
    }


# ============================================================
# PROMPT SELECTION
# ============================================================

PROMPT_FILES = {
    "F0": "nl_to_fol.txt",
    "F1": "nl_to_fol_F1.txt",
    "F2": "nl_to_fol_F2.txt",
}


def build_fol_prompt(prompt_tier, condition, premise, hypothesis,
                     gold_label=None, item_id=None):
    """Build the full prompt with condition-specific content.

    prompt_tier: "F0", "F1", or "F2"
    condition: "c1", "c2", "c3", or "c4"
    """
    filename = PROMPT_FILES.get(prompt_tier, "nl_to_fol.txt")
    template = (PROMPT_DIR / filename).read_text(encoding="utf-8")

    # Prepare condition-specific values
    phase1_label = ""
    phase1_explanation = ""
    if condition in ("c2", "c4") and item_id:
        p1 = get_phase1_prediction(item_id)
        phase1_label = p1["label"]
        phase1_explanation = p1["explanation"]

    # Fill template
    prompt = template.format(
        premise=premise,
        hypothesis=hypothesis,
        gold_label=gold_label or "",
        phase1_label=phase1_label,
        phase1_explanation=phase1_explanation,
    )

    # For C1 (blind), strip the condition block so LLM gets no hints
    if condition == "c1" and prompt_tier != "F0":
        # Remove everything between === CONDITION === and === END CONDITION ===
        import re
        prompt = re.sub(
            r"=== CONDITION.*?=== END CONDITION ===\s*",
            "", prompt, flags=re.DOTALL)

    return prompt


# ============================================================
# FOL TRANSLATION
# ============================================================

def load_prompt(name):
    return (PROMPT_DIR / name).read_text(encoding="utf-8")


def translate_to_fol(client, model, premise, hypothesis,
                     prompt_tier="F0", condition="c1",
                     gold_label=None, item_id=None):
    """Ask LLM to translate P, H into FOL (Prover9 syntax)."""
    prompt = build_fol_prompt(prompt_tier, condition, premise, hypothesis,
                              gold_label=gold_label, item_id=item_id)
    messages = [
        {"role": "system", "content": "You are an expert in first-order logic and formal semantics."},
        {"role": "user", "content": prompt},
    ]
    return call_llm(client, model, messages, max_tokens=FOL_MAX_TOKENS)


def parse_fol_output(raw_text):
    """Parse LLM's FOL output into premises list and hypothesis string."""
    lines = raw_text.strip().split("\n")
    premises = []
    hypothesis = None
    mode = None

    for line in lines:
        line = line.strip()
        if not line:
            continue
        if line.lower().startswith("premises") or line.lower().startswith("premise"):
            mode = "premises"
            continue
        if line.lower().startswith("hypothesis"):
            mode = "hypothesis"
            continue
        if line.startswith("-") or line.startswith("*"):
            line = line.lstrip("-* ").strip()

        if mode == "premises" and line:
            premises.append(line.rstrip("."))
        elif mode == "hypothesis" and line:
            hypothesis = line.rstrip(".")

    return premises, hypothesis


# ============================================================
# PROVER9 / MACE4 INTERFACE
# ============================================================

def build_prover9_input(premises, hypothesis, mode="prove"):
    """Build Prover9/MACE4 input file content.

    mode="prove": check if premises entail hypothesis (Prover9)
    mode="counter": search for countermodel to premises ∧ ¬hypothesis (MACE4)
    """
    lines = ["formulas(assumptions).\n"]
    for p in premises:
        lines.append(f"  {p}.\n")
    lines.append("end_of_list.\n\n")

    if mode == "prove":
        lines.append("formulas(goals).\n")
        lines.append(f"  {hypothesis}.\n")
        lines.append("end_of_list.\n")
    else:  # counter
        lines.append("formulas(goals).\n")
        lines.append(f"  {hypothesis}.\n")
        lines.append("end_of_list.\n")

    return "".join(lines)


def run_prover9(premises, hypothesis, timeout=None):
    """Run Prover9. Returns (success: bool, output: str)."""
    timeout = timeout or PROVER_TIMEOUT
    input_text = build_prover9_input(premises, hypothesis, mode="prove")

    with tempfile.NamedTemporaryFile(mode="w", suffix=".in", delete=False) as f:
        f.write(input_text)
        input_file = f.name

    try:
        result = subprocess.run(
            [PROVER9_PATH, "-t", str(timeout), "-f", input_file],
            capture_output=True, text=True, timeout=timeout + 10
        )
        output = result.stdout + result.stderr
        proved = "THEOREM PROVED" in output
        return proved, output
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT"
    except FileNotFoundError:
        return False, f"ERROR: {PROVER9_PATH} not found. Install Prover9 or set PROVER9_PATH."
    finally:
        os.unlink(input_file)


def run_mace4(premises, hypothesis, timeout=None):
    """Run MACE4 to find countermodel. Returns (found: bool, output: str)."""
    timeout = timeout or PROVER_TIMEOUT
    input_text = build_prover9_input(premises, hypothesis, mode="counter")

    with tempfile.NamedTemporaryFile(mode="w", suffix=".in", delete=False) as f:
        f.write(input_text)
        input_file = f.name

    try:
        result = subprocess.run(
            [MACE4_PATH, "-t", str(timeout), "-f", input_file],
            capture_output=True, text=True, timeout=timeout + 10
        )
        output = result.stdout + result.stderr
        found = "Exiting with 1 model" in output or "exit (max_models)" in output
        return found, output
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT"
    except FileNotFoundError:
        return False, f"ERROR: {MACE4_PATH} not found. Install MACE4 or set MACE4_PATH."
    finally:
        os.unlink(input_file)


def syntax_check_fol(premises, hypothesis):
    """Quick syntax check: try to parse as Prover9 input.
    Returns (ok: bool, error_msg: str or None)."""
    input_text = build_prover9_input(premises, hypothesis)
    with tempfile.NamedTemporaryFile(mode="w", suffix=".in", delete=False) as f:
        f.write(input_text)
        input_file = f.name
    try:
        # Use Prover9 with very short timeout just to check parsing
        result = subprocess.run(
            [PROVER9_PATH, "-t", "1", "-f", input_file],
            capture_output=True, text=True, timeout=5
        )
        output = result.stdout + result.stderr
        if "Fatal error" in output or "parse error" in output.lower():
            return False, output
        return True, None
    except FileNotFoundError:
        # If prover9 not installed, do basic regex check
        return _regex_syntax_check(premises, hypothesis)
    except Exception as e:
        return False, str(e)
    finally:
        os.unlink(input_file)


def _regex_syntax_check(premises, hypothesis):
    """Fallback syntax check when Prover9 is not installed."""
    all_formulas = premises + [hypothesis]
    for f in all_formulas:
        # Check balanced parentheses
        if f.count("(") != f.count(")"):
            return False, f"Unbalanced parentheses in: {f}"
        # Check for common issues
        if not f.strip():
            return False, "Empty formula"
    return True, None


# ============================================================
# VERIFICATION LOOP (Phase 3)
# ============================================================

def fix_fol(client, model, premise, hypothesis, previous_fol, error_message):
    """Ask LLM to fix FOL based on error feedback."""
    template = load_prompt("fol_fix.txt")
    prompt = template.format(
        premise=premise, hypothesis=hypothesis,
        previous_fol=previous_fol, error_message=error_message,
    )
    messages = [
        {"role": "system", "content": "You are an expert in first-order logic. Fix the errors."},
        {"role": "user", "content": prompt},
    ]
    return call_llm(client, model, messages, max_tokens=FOL_MAX_TOKENS)


def run_fol_pipeline(client, model, premise, hypothesis, max_retries=None,
                     prompt_tier="F0", condition="c1",
                     gold_label=None, item_id=None):
    """Full pipeline with verification loop.

    Returns dict with:
        - fol_premises, fol_hypothesis: final FOL
        - proved, countermodel: prover results
        - label: "entailment" / "contradiction" / "unknown"
        - attempts: number of attempts used
        - errors: list of error messages from failed attempts
    """
    max_retries = max_retries or MAX_RETRIES
    errors = []

    for attempt in range(1, max_retries + 1):
        # Step 1: Get FOL translation
        if attempt == 1:
            raw = translate_to_fol(client, model, premise, hypothesis,
                                   prompt_tier=prompt_tier, condition=condition,
                                   gold_label=gold_label, item_id=item_id)
        else:
            raw = fix_fol(client, model, premise, hypothesis,
                         previous_raw, errors[-1])

        previous_raw = raw
        premises, hyp = parse_fol_output(raw)

        if not premises or not hyp:
            errors.append(f"Parse error: could not extract premises/hypothesis from LLM output:\n{raw}")
            continue

        # Step 2: Syntax check
        ok, err = syntax_check_fol(premises, hyp)
        if not ok:
            errors.append(f"Syntax error: {err}")
            continue

        # Step 3: Run Prover9 (entailment)
        proved, prover_output = run_prover9(premises, hyp)
        if proved:
            return {
                "fol_premises": premises, "fol_hypothesis": hyp,
                "proved": True, "countermodel": False,
                "label": "entailment", "attempts": attempt,
                "errors": errors, "raw_fol": raw,
            }

        # Step 4: Run MACE4 (countermodel)
        found, mace_output = run_mace4(premises, hyp)
        if found:
            return {
                "fol_premises": premises, "fol_hypothesis": hyp,
                "proved": False, "countermodel": True,
                "label": "non-entailment", "attempts": attempt,
                "errors": errors, "raw_fol": raw,
            }

        # Neither proved nor countermodel — record and retry
        errors.append(f"Prover9: no proof. MACE4: no countermodel. Timeout or undecidable.")

    # All attempts exhausted
    return {
        "fol_premises": premises if premises else [],
        "fol_hypothesis": hyp or "",
        "proved": False, "countermodel": False,
        "label": "unknown", "attempts": max_retries,
        "errors": errors, "raw_fol": raw if 'raw' in dir() else "",
    }


# ============================================================
# BATCH RUNNER
# ============================================================

def run_batch(items, client, model, output_file=None,
              prompt_tier="F0", condition="c1"):
    """Run FOL pipeline on a list of NLI items.

    items: list of dicts with 'premise', 'hypothesis', 'gold' keys
    Returns list of result dicts.
    """
    results = []
    for i, item in enumerate(items):
        print(f"[{i+1}/{len(items)}] {item.get('id', i+1)}: ", end="", flush=True)

        result = run_fol_pipeline(client, model,
                                  item["premise"], item["hypothesis"],
                                  prompt_tier=prompt_tier, condition=condition,
                                  gold_label=item.get("gold"),
                                  item_id=item.get("id"))
        result["id"] = item.get("id", i+1)
        result["gold"] = item.get("gold", "")
        result["premise_nl"] = item["premise"]
        result["hypothesis_nl"] = item["hypothesis"]

        correct = (
            (result["label"] == "entailment" and item.get("gold") in ("yes", "entailment")) or
            (result["label"] == "non-entailment" and item.get("gold") in ("no", "unknown", "contradiction", "neutral"))
        )
        result["correct"] = correct

        status = "✓" if correct else "✗"
        print(f"{result['label']} (attempt {result['attempts']}) {status}")

        results.append(result)
        time.sleep(0.5)

    # Save results
    if output_file:
        with open(output_file, "w", encoding="utf-8") as f:
            json.dump(results, f, indent=2, ensure_ascii=False)
        print(f"\nResults saved to {output_file}")

    # Summary
    total = len(results)
    correct = sum(1 for r in results if r["correct"])
    proved = sum(1 for r in results if r["proved"])
    counter = sum(1 for r in results if r["countermodel"])
    unknown = sum(1 for r in results if r["label"] == "unknown")
    avg_attempts = sum(r["attempts"] for r in results) / total if total else 0

    print(f"\n--- Summary ({model}) ---")
    print(f"Total: {total}")
    print(f"Proved: {proved}, Countermodel: {counter}, Unknown: {unknown}")
    print(f"Accuracy: {correct}/{total} ({correct/total:.1%})")
    print(f"Avg attempts: {avg_attempts:.1f}")

    return results


# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="NESTOR FOL Pipeline")
    parser.add_argument("--data", default="../data/fracas/fracas.xml",
                        help="Path to dataset (FraCaS XML or JSON)")
    parser.add_argument("--model", default="gpt-4o",
                        help="Model key (see clients/models.py)")
    parser.add_argument("--output", default=None,
                        help="Output JSON file")
    parser.add_argument("--limit", type=int, default=None,
                        help="Max items to process")
    parser.add_argument("--section", default=None,
                        help="FraCaS section filter (e.g. '1' for quantifiers)")
    parser.add_argument("--prompt", default="F0", choices=["F0", "F1", "F2"],
                        help="Prompt tier: F0 (bare), F1 (conventions), F2 (Davidsonian)")
    parser.add_argument("--condition", default="c1", choices=["c1", "c2", "c3", "c4"],
                        help="Condition: c1 (blind), c2 (phase1 pred), c3 (gold), c4 (phase1+expl)")
    args = parser.parse_args()

    # Load data
    if args.data.endswith(".xml"):
        items = load_flat(args.data)
    else:
        with open(args.data) as f:
            items = json.load(f)

    if args.section:
        items = [it for it in items if it["id"].split("-")[1].startswith(args.section)]

    if args.limit:
        items = items[:args.limit]

    print(f"Loaded {len(items)} items from {args.data}")
    print(f"Model: {args.model}, Prompt: {args.prompt}, Condition: {args.condition}\n")

    # Setup client
    client = get_client(args.model)

    # Run
    output = args.output or f"results/fol_{args.prompt}_{args.condition}_{args.model}_{len(items)}items.json"
    run_batch(items, client, args.model, output_file=output,
              prompt_tier=args.prompt, condition=args.condition)
