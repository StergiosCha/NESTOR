"""
NESTOR Phase 2 -- Coq Pipeline
==============================
NL -> Coq (via LLM) -> coqc -> result

Prompt tiers:
  T0: Syntax rules only (Montague-style Entity -> Prop)
  T1: T0 + Montague.v foundation file
  T2: T0 + section-matched foundation files
  T3: T0 + rich context (more files per section)

Conditions:
  C1 (blind): No label given. LLM decides the relation.
  C2 (Phase 1 prediction): LLM gets Phase 1 predicted label.
  C3 (gold label): LLM gets the gold label.
  C4 (Phase 1 + explanation): LLM gets Phase 1 label + NL explanation.

Two approaches:
  Direct: Formalise P, H directly. Proof IS the explanation.
  Valentino: Formalise the LLM's explanation E. Check P U E |= H.

Verification loop:
  If coqc fails, feed error back to LLM, retry up to k=3.

Requirements:
  pip install openai python-dotenv
  coqc in PATH (Coq 8.18+ recommended)
"""

import json
import os
import re
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

COQC_PATH = os.environ.get("COQC_PATH", "coqc")
COQ_TIMEOUT = int(os.environ.get("COQ_TIMEOUT", "60") or 60)
MAX_RETRIES = int(os.environ.get("MAX_RETRIES", "3") or 3)

PROMPT_DIR = Path(__file__).parent / "prompts"
FOUNDATIONS_DIR = Path(__file__).resolve().parent.parent / "coq_foundations"

COQ_MAX_TOKENS = 2500


# ============================================================
# PHASE 1 RESULTS (for C2/C4 conditions)
# ============================================================

PHASE1_RESULTS_PATH = (
    Path(__file__).resolve().parent.parent
    / "phase1_nli_eval" / "results" / "fracas_results_azure.json"
)

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
    """Get Phase 1 prediction and explanation for an item.

    fracas_results_azure.json is keyed: model -> item_number
    Item IDs look like "fracas-1-023", item_number is "23" (no leading zero).
    """
    results = load_phase1_results()
    # Extract the number from the item ID
    if "-" in str(item_id):
        item_num = str(int(item_id.split("-")[-1]))
    else:
        item_num = str(item_id)
    model_results = results.get(model, {})
    entry = model_results.get(item_num, {})
    return {
        "label": entry.get("predicted", "unknown"),
        "explanation": entry.get("explanation", ""),
    }


# ============================================================
# PROMPT TIER & SECTION MAPPING
# ============================================================

PROMPT_FILES = {
    "T0": "nl_to_coq_T0.txt",
    "T1": "nl_to_coq_T1.txt",
    "T2": "nl_to_coq_T2.txt",
    "T3": "nl_to_coq_T3.txt",
}

# T2: 1-2 foundation files per section
SECTION_FILES = {
    "1": ["Montague.v", "BarwiseCooper.v"],
    "2": ["Link1983.v", "Montague.v"],
    "3": ["DonkeyScope.v", "Montague.v"],
    "4": ["Montague.v"],
    "5": ["AdjectivesExtension.v", "MTT_base.v"],
    "6": ["AdjectivesExtension.v", "Montague.v"],
    "7": ["DowtyTense.v", "Montague.v"],
    "8": ["PTQ.v", "kratzer2.v"],
    "9": ["MTT_base.v", "Montague.v"],
}

# T3: more files per section (richer context)
SECTION_FILES_T3 = {
    "1": ["Montague.v", "BarwiseCooper.v", "Quantifiers.v", "DonkeyScope.v"],
    "2": ["Link1983.v", "Montague.v", "champollion_full.v"],
    "3": ["DonkeyScope.v", "Montague.v", "BarwiseCooper.v"],
    "4": ["Montague.v"],
    "5": ["AdjectivesExtension.v", "MTT_base.v", "Quantifiers.v"],
    "6": ["AdjectivesExtension.v", "Montague.v", "MTT_base.v"],
    "7": ["DowtyTense.v", "Montague.v", "Aspect.v", "ImperfectiveParadox.v"],
    "8": ["PTQ.v", "kratzer2.v", "PTQ_deep.v"],
    "9": ["MTT_base.v", "Montague.v"],
}


def get_section_from_id(item_id):
    """Extract FraCaS section number from item ID.

    "fracas-1-023" -> "1"
    "fracas-5-201" -> "5"
    """
    parts = str(item_id).split("-")
    if len(parts) >= 2:
        return parts[1]
    return "1"  # fallback


def load_foundation_files(file_list):
    """Load foundation .v files and concatenate them with delimiters."""
    context = ""
    for fname in file_list:
        fpath = FOUNDATIONS_DIR / fname
        if fpath.exists():
            content = fpath.read_text(encoding="utf-8")
            context += f"--- BEGIN {fname} ---\n"
            context += content
            context += f"\n--- END {fname} ---\n\n"
        else:
            context += f"--- {fname} NOT FOUND (skipped) ---\n\n"
    return context


def build_coq_prompt(prompt_tier, condition, premise, hypothesis,
                     gold_label=None, item_id=None):
    """Build the full Coq prompt with condition-specific content.

    prompt_tier: "T0", "T1", "T2", or "T3"
    condition: "c1", "c2", "c3", or "c4"
    """
    filename = PROMPT_FILES.get(prompt_tier, "nl_to_coq_T0.txt")
    template = (PROMPT_DIR / filename).read_text(encoding="utf-8")

    # Prepare condition-specific values
    phase1_label = ""
    phase1_explanation = ""
    if condition in ("c2", "c4") and item_id:
        p1 = get_phase1_prediction(item_id)
        phase1_label = p1["label"]
        phase1_explanation = p1["explanation"]

    # Prepare foundation file content for T1/T2/T3
    montague_v = ""
    foundation_files = ""
    section = get_section_from_id(item_id) if item_id else "1"

    if prompt_tier == "T1":
        montague_path = FOUNDATIONS_DIR / "Montague.v"
        if montague_path.exists():
            montague_v = montague_path.read_text(encoding="utf-8")

    elif prompt_tier == "T2":
        files = SECTION_FILES.get(section, ["Montague.v"])
        foundation_files = load_foundation_files(files)

    elif prompt_tier == "T3":
        files = SECTION_FILES_T3.get(section, ["Montague.v"])
        foundation_files = load_foundation_files(files)

    # Fill template placeholders
    prompt = template.format(
        premise=premise,
        hypothesis=hypothesis,
        gold_label=gold_label or "",
        phase1_label=phase1_label,
        phase1_explanation=phase1_explanation,
        montague_v=montague_v,
        foundation_files=foundation_files,
    )

    # For C1 (blind), strip the condition block so LLM gets no hints
    if condition == "c1":
        prompt = re.sub(
            r"=== CONDITION.*?=== END CONDITION ===\s*",
            "", prompt, flags=re.DOTALL)

    return prompt


# ============================================================
# COQ TRANSLATION
# ============================================================

def load_prompt(name):
    return (PROMPT_DIR / name).read_text(encoding="utf-8")


def extract_coq_code(raw_text):
    """Extract Coq code from LLM output (handles ```coq blocks)."""
    # Try to find code block
    match = re.search(r"```(?:coq)?\s*\n(.*?)```", raw_text, re.DOTALL)
    if match:
        return match.group(1).strip()
    # If no code block, assume the whole thing is Coq
    # Strip any obvious non-Coq lines
    lines = raw_text.strip().split("\n")
    coq_lines = []
    for line in lines:
        # Skip lines that look like natural language commentary
        if line.strip().startswith("This") or line.strip().startswith("Here"):
            continue
        coq_lines.append(line)
    return "\n".join(coq_lines).strip()


def translate_to_coq_direct(client, model, premise, hypothesis,
                            prompt_tier="T0", condition="c1",
                            gold_label=None, item_id=None):
    """Direct approach: formalise P, H in Coq using prompt tier and condition."""
    prompt = build_coq_prompt(prompt_tier, condition, premise, hypothesis,
                              gold_label=gold_label, item_id=item_id)
    messages = [
        {"role": "system",
         "content": "You are an expert in Coq and formal semantics. Output only valid Coq code."},
        {"role": "user", "content": prompt},
    ]
    raw = call_llm(client, model, messages, max_tokens=COQ_MAX_TOKENS)
    return extract_coq_code(raw), raw


def translate_to_coq_valentino(client, model, premise, hypothesis, explanation):
    """Valentino approach: formalise explanation E, prove P U E |= H."""
    template = load_prompt("valentino_coq.txt")
    prompt = template.format(
        premise=premise, hypothesis=hypothesis, explanation=explanation)
    messages = [
        {"role": "system",
         "content": "You are an expert in Coq and formal semantics. Output only valid Coq code."},
        {"role": "user", "content": prompt},
    ]
    raw = call_llm(client, model, messages, max_tokens=COQ_MAX_TOKENS)
    return extract_coq_code(raw), raw


# ============================================================
# COQ COMPILER
# ============================================================

def run_coqc(coq_code, timeout=None):
    """Compile Coq code with coqc.

    Returns:
        compiled: bool -- did it compile without errors?
        proof_complete: bool -- was the proof completed (no Abort)?
        output: str -- compiler output (errors etc.)
    """
    timeout = timeout or COQ_TIMEOUT

    with tempfile.NamedTemporaryFile(mode="w", suffix=".v", delete=False,
                                      encoding="utf-8") as f:
        f.write(coq_code)
        coq_file = f.name

    try:
        result = subprocess.run(
            [COQC_PATH, coq_file],
            capture_output=True, text=True, timeout=timeout,
        )
        output = result.stdout + result.stderr
        compiled = result.returncode == 0
        proof_complete = compiled and "Abort" not in coq_code
        return compiled, proof_complete, output
    except subprocess.TimeoutExpired:
        return False, False, "TIMEOUT"
    except FileNotFoundError:
        return False, False, f"ERROR: {COQC_PATH} not found. Install Coq."
    finally:
        # Clean up .v and .vo files
        for ext in [".v", ".vo", ".vok", ".vos", ".glob"]:
            p = coq_file.replace(".v", ext)
            if os.path.exists(p):
                os.unlink(p)


def extract_coq_label(coq_code):
    """Extract the NLI label from compiled Coq code.

    Logic:
      - If entailment theorem has Qed -> "entailment"
      - If contradiction theorem has Qed -> "contradiction"
      - If both Abort -> "neutral"
      - Fallback heuristic for single-theorem files
    """
    # Use negative lookahead (?!Theorem) to avoid crossing into the
    # next theorem block. Without this, "Theorem entailment...Abort...
    # Theorem contradiction...Qed" would falsely match entailment->Qed.
    has_entailment_qed = bool(re.search(
        r"Theorem\s+entailment\b(?:(?!Theorem).)*?Qed\.",
        coq_code, re.DOTALL))
    has_contradiction_qed = bool(re.search(
        r"Theorem\s+contradiction\b(?:(?!Theorem).)*?Qed\.",
        coq_code, re.DOTALL))

    if has_entailment_qed and not has_contradiction_qed:
        return "entailment"
    if has_contradiction_qed and not has_entailment_qed:
        return "contradiction"
    if not has_entailment_qed and not has_contradiction_qed:
        return "neutral"

    # Both Qed -- should not happen but fall back to entailment
    return "entailment"


# ============================================================
# VERIFICATION LOOP
# ============================================================

def fix_coq(client, model, premise, hypothesis, label, previous_coq,
            error_message):
    """Ask LLM to fix Coq code based on compiler error."""
    template = load_prompt("coq_fix.txt")
    prompt = template.format(
        premise=premise, hypothesis=hypothesis, label=label,
        previous_coq=previous_coq, error_message=error_message,
    )
    messages = [
        {"role": "system",
         "content": "You are an expert in Coq. Fix the compilation errors."},
        {"role": "user", "content": prompt},
    ]
    raw = call_llm(client, model, messages, max_tokens=COQ_MAX_TOKENS)
    return extract_coq_code(raw), raw


def run_coq_pipeline(client, model, premise, hypothesis, label,
                     approach="direct", explanation=None, max_retries=None,
                     prompt_tier="T0", condition="c1",
                     gold_label=None, item_id=None):
    """Full Coq pipeline with verification loop.

    approach: "direct" or "valentino"
    prompt_tier: "T0", "T1", "T2", "T3"
    condition: "c1", "c2", "c3", "c4"
    """
    max_retries = max_retries or MAX_RETRIES
    errors = []

    for attempt in range(1, max_retries + 1):
        # Step 1: Get Coq code
        if attempt == 1:
            if approach == "direct":
                coq_code, raw = translate_to_coq_direct(
                    client, model, premise, hypothesis,
                    prompt_tier=prompt_tier, condition=condition,
                    gold_label=gold_label, item_id=item_id)
            else:
                coq_code, raw = translate_to_coq_valentino(
                    client, model, premise, hypothesis, explanation)
        else:
            coq_code, raw = fix_coq(
                client, model, premise, hypothesis, label,
                previous_code, errors[-1])

        previous_code = coq_code

        if not coq_code.strip():
            errors.append("Empty Coq code returned by LLM.")
            continue

        # Step 2: Compile
        compiled, proof_complete, output = run_coqc(coq_code)

        # Extract the label the LLM chose from the Coq code structure
        predicted_label = extract_coq_label(coq_code)

        if compiled and proof_complete:
            return {
                "coq_code": coq_code,
                "compiled": True, "proof_complete": True,
                "predicted_label": predicted_label,
                "approach": approach,
                "attempts": attempt, "errors": errors,
            }

        if compiled and not proof_complete:
            # Compiled but proof was Aborted
            return {
                "coq_code": coq_code,
                "compiled": True, "proof_complete": False,
                "predicted_label": predicted_label,
                "approach": approach,
                "attempts": attempt, "errors": errors,
            }

        # Compilation failed -- extract error for feedback
        errors.append(output[:1000])  # truncate long errors

    return {
        "coq_code": coq_code if coq_code else "",
        "compiled": False, "proof_complete": False,
        "predicted_label": "error",
        "approach": approach,
        "attempts": max_retries, "errors": errors,
    }


# ============================================================
# BATCH RUNNER
# ============================================================

def run_batch(items, client, model, approach="direct", output_file=None,
              prompt_tier="T0", condition="c1"):
    """Run Coq pipeline on a list of NLI items."""
    results = []
    for i, item in enumerate(items):
        print(f"[{i+1}/{len(items)}] {item.get('id', i+1)}: ", end="",
              flush=True)

        result = run_coq_pipeline(
            client, model,
            item["premise"], item["hypothesis"],
            item.get("gold", "entailment"),
            approach=approach,
            explanation=item.get("explanation"),
            prompt_tier=prompt_tier,
            condition=condition,
            gold_label=item.get("gold"),
            item_id=item.get("id"),
        )
        result["id"] = item.get("id", i+1)
        result["gold"] = item.get("gold", "")
        result["premise_nl"] = item["premise"]
        result["hypothesis_nl"] = item["hypothesis"]

        # Check correctness
        pred = result.get("predicted_label", "")
        gold = item.get("gold", "")
        correct = (
            (pred == "entailment" and gold in ("yes", "entailment"))
            or (pred == "contradiction" and gold in ("no", "contradiction"))
            or (pred == "neutral" and gold in ("unknown", "neutral", "undef"))
        )
        result["correct"] = correct

        status = "compiled" if result["compiled"] else "FAILED"
        if result["proof_complete"]:
            status = "PROVED"
        tag = "+" if correct else "-"
        print(f"{status} [{pred}] (attempt {result['attempts']}) {tag}")

        results.append(result)
        time.sleep(0.5)

    if output_file:
        os.makedirs(os.path.dirname(output_file) or ".", exist_ok=True)
        with open(output_file, "w", encoding="utf-8") as f:
            json.dump(results, f, indent=2, ensure_ascii=False)
        print(f"\nResults saved to {output_file}")

    # Summary
    total = len(results)
    compiled = sum(1 for r in results if r["compiled"])
    proved = sum(1 for r in results if r["proof_complete"])
    correct_n = sum(1 for r in results if r.get("correct"))
    avg_attempts = (sum(r["attempts"] for r in results) / total
                    if total else 0)

    print(f"\n--- Summary ({model}, {approach}, {prompt_tier}, {condition}) ---")
    print(f"Total: {total}")
    print(f"Compiled: {compiled}/{total} ({compiled/total:.1%})")
    print(f"Proof complete: {proved}/{total} ({proved/total:.1%})")
    print(f"Correct: {correct_n}/{total} ({correct_n/total:.1%})")
    print(f"Avg attempts: {avg_attempts:.1f}")

    return results


# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":
    import argparse
    from clients.models import MODELS

    parser = argparse.ArgumentParser(description="NESTOR Coq Pipeline")
    parser.add_argument("--data", default="../data/fracas/fracas.xml",
                        help="Path to dataset (FraCaS XML or JSON)")
    parser.add_argument("--model", default="gpt-4o",
                        help="Model key (see clients/models.py)")
    parser.add_argument("--approach", default="direct",
                        choices=["direct", "valentino"],
                        help="Coq approach: direct or valentino")
    parser.add_argument("--output", default=None,
                        help="Output JSON file")
    parser.add_argument("--limit", type=int, default=None,
                        help="Max items to process")
    parser.add_argument("--section", default=None,
                        help="FraCaS section filter (e.g. '1' for quantifiers)")
    parser.add_argument("--tier", default="T0",
                        choices=["T0", "T1", "T2", "T3"],
                        help="Prompt tier: T0 (syntax), T1 (+Montague.v), "
                             "T2 (+section files), T3 (+rich context)")
    parser.add_argument("--condition", default="c1",
                        choices=["c1", "c2", "c3", "c4"],
                        help="Condition: c1 (blind), c2 (phase1 pred), "
                             "c3 (gold), c4 (phase1+expl)")
    args = parser.parse_args()

    # Only check vars needed for the selected model
    required = [("AZURE_API_KEY", os.environ.get("AZURE_API_KEY", ""))]
    if MODELS.get(args.model, {}).get("provider") == "azure-openai":
        required.append(("AZURE_OPENAI_ENDPOINT",
                         os.environ.get("AZURE_OPENAI_ENDPOINT", "")))
    elif MODELS.get(args.model, {}).get("provider") == "azure-ai":
        required.append(("AZURE_AI_ENDPOINT",
                         os.environ.get("AZURE_AI_ENDPOINT", "")))
    missing = [name for name, val in required if not val]
    if missing:
        print(f"ERROR: missing required env vars: {', '.join(missing)}")
        print("  copy .env.example to .env and fill in values")
        sys.exit(1)

    items = (load_flat(args.data) if args.data.endswith(".xml")
             else json.load(open(args.data)))
    if args.section:
        items = [it for it in items
                 if it["id"].split("-")[1].startswith(args.section)]
    if args.limit:
        items = items[:args.limit]

    print(f"Loaded {len(items)} items from {args.data}")
    print(f"Model: {args.model}, Tier: {args.tier}, "
          f"Condition: {args.condition}, Approach: {args.approach}\n")

    client = get_client(args.model)
    output = (args.output
              or f"results/coq_{args.tier}_{args.condition}_{args.model}"
                 f"_{len(items)}items.json")
    run_batch(items, client, args.model, approach=args.approach,
              output_file=output,
              prompt_tier=args.tier, condition=args.condition)
