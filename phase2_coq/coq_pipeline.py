"""
NESTOR Phase 2 — Coq Pipeline
==============================
NL → Coq (via LLM) → coqc → result

Two approaches:
  Direct (C3/C4): Formalise P, H directly. Proof IS the explanation.
  Valentino: Formalise the LLM's explanation E. Check P ∪ E ⊨ H.

Verification loop (Phase 3):
If coqc fails, feed error back to LLM, retry up to k=3.

Requirements:
  pip install openai
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
from openai import AzureOpenAI, OpenAI

load_dotenv()

# Load environemnt variables
API_KEY = os.environ.get("AZURE_API_KEY", "")
OPENAI_ENDPOINT = os.environ.get("AZURE_OPENAI_ENDPOINT", "")
OPENAI_API_VERSION = os.environ.get("AZURE_OPENAI_API_VERSION", "")
AZURE_AI_ENDPOINT = os.environ.get("AZURE_AI_ENDPOINT", "")
COQC_PATH = os.environ.get("COQC_PATH", "")
COQ_TIMEOUT = int(os.environ.get("COQ_TIMEOUT", "0") or 0)
MAX_RETRIES = int(os.environ.get("MAX_RETRIES", "0") or 0)

PROMPT_DIR = Path(__file__).parent / "prompts"

# ============================================================
# LLM CLIENTS
# ============================================================

def get_azure_client():
    return AzureOpenAI(
        api_version=OPENAI_API_VERSION,
        azure_endpoint=OPENAI_ENDPOINT,
        api_key=API_KEY,
    )

def get_ai_client():
    return OpenAI(base_url=AZURE_AI_ENDPOINT, api_key=API_KEY)

def call_llm(client, model, messages, temperature=0.0, max_tokens=1000):
    resp = client.chat.completions.create(
        model=model, messages=messages,
        temperature=temperature, max_tokens=max_tokens,
    )
    return resp.choices[0].message.content


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


def translate_to_coq_direct(client, model, premise, hypothesis, label):
    """Direct approach: formalise P, H in Coq."""
    template = load_prompt("nl_to_coq.txt")
    prompt = template.format(premise=premise, hypothesis=hypothesis, label=label)
    messages = [
        {"role": "system", "content": "You are an expert in Coq and formal semantics. Output only valid Coq code."},
        {"role": "user", "content": prompt},
    ]
    raw = call_llm(client, model, messages)
    return extract_coq_code(raw), raw


def translate_to_coq_valentino(client, model, premise, hypothesis, explanation):
    """Valentino approach: formalise explanation E, prove P ∪ E ⊨ H."""
    template = load_prompt("valentino_coq.txt")
    prompt = template.format(premise=premise, hypothesis=hypothesis, explanation=explanation)
    messages = [
        {"role": "system", "content": "You are an expert in Coq and formal semantics. Output only valid Coq code."},
        {"role": "user", "content": prompt},
    ]
    raw = call_llm(client, model, messages)
    return extract_coq_code(raw), raw


# ============================================================
# COQ COMPILER
# ============================================================

def run_coqc(coq_code, timeout=None):
    """Compile Coq code with coqc.

    Returns:
        compiled: bool — did it compile without errors?
        proof_complete: bool — was the proof completed (no Abort)?
        output: str — compiler output (errors etc.)
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


# ============================================================
# VERIFICATION LOOP
# ============================================================

def fix_coq(client, model, premise, hypothesis, label, previous_coq, error_message):
    """Ask LLM to fix Coq code based on compiler error."""
    template = load_prompt("coq_fix.txt")
    prompt = template.format(
        premise=premise, hypothesis=hypothesis, label=label,
        previous_coq=previous_coq, error_message=error_message,
    )
    messages = [
        {"role": "system", "content": "You are an expert in Coq. Fix the compilation errors."},
        {"role": "user", "content": prompt},
    ]
    raw = call_llm(client, model, messages)
    return extract_coq_code(raw), raw


def run_coq_pipeline(client, model, premise, hypothesis, label,
                     approach="direct", explanation=None, max_retries=None):
    """Full Coq pipeline with verification loop.

    approach: "direct" or "valentino"
    """
    max_retries = max_retries or MAX_RETRIES
    errors = []

    for attempt in range(1, max_retries + 1):
        # Step 1: Get Coq code
        if attempt == 1:
            if approach == "direct":
                coq_code, raw = translate_to_coq_direct(
                    client, model, premise, hypothesis, label)
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

        if compiled and proof_complete:
            return {
                "coq_code": coq_code,
                "compiled": True, "proof_complete": True,
                "approach": approach,
                "attempts": attempt, "errors": errors,
            }

        if compiled and not proof_complete:
            # Compiled but proof was Aborted — the LLM is saying it can't prove it
            return {
                "coq_code": coq_code,
                "compiled": True, "proof_complete": False,
                "approach": approach,
                "attempts": attempt, "errors": errors,
            }

        # Compilation failed — extract error for feedback
        errors.append(output[:1000])  # truncate long errors

    return {
        "coq_code": coq_code if coq_code else "",
        "compiled": False, "proof_complete": False,
        "approach": approach,
        "attempts": max_retries, "errors": errors,
    }


# ============================================================
# BATCH RUNNER
# ============================================================

def run_batch(items, client, model, approach="direct", output_file=None):
    """Run Coq pipeline on a list of NLI items."""
    results = []
    for i, item in enumerate(items):
        print(f"[{i+1}/{len(items)}] {item.get('id', i+1)}: ", end="", flush=True)

        result = run_coq_pipeline(
            client, model,
            item["premise"], item["hypothesis"],
            item.get("gold", "entailment"),
            approach=approach,
            explanation=item.get("explanation"),
        )
        result["id"] = item.get("id", i+1)
        result["gold"] = item.get("gold", "")
        result["premise_nl"] = item["premise"]
        result["hypothesis_nl"] = item["hypothesis"]

        status = "compiled" if result["compiled"] else "FAILED"
        if result["proof_complete"]:
            status = "PROVED"
        print(f"{status} (attempt {result['attempts']})")

        results.append(result)
        time.sleep(0.5)

    if output_file:
        with open(output_file, "w", encoding="utf-8") as f:
            json.dump(results, f, indent=2, ensure_ascii=False)
        print(f"\nResults saved to {output_file}")

    # Summary
    total = len(results)
    compiled = sum(1 for r in results if r["compiled"])
    proved = sum(1 for r in results if r["proof_complete"])
    avg_attempts = sum(r["attempts"] for r in results) / total if total else 0

    print(f"\n--- Summary ({model}, {approach}) ---")
    print(f"Total: {total}")
    print(f"Compiled: {compiled}/{total} ({compiled/total:.1%})")
    print(f"Proof complete: {proved}/{total} ({proved/total:.1%})")
    print(f"Avg attempts: {avg_attempts:.1f}")

    return results


# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":
    import argparse
    import sys
    sys.path.insert(0, str(Path(__file__).parent.parent / "phase2_fol"))
    from fol_pipeline import load_fracas

    parser = argparse.ArgumentParser(description="NESTOR Coq Pipeline")
    parser.add_argument("--data", default="../data/fracas/fracas.xml")
    parser.add_argument("--model", default="gpt-4o")
    parser.add_argument("--client", default="azure", choices=["azure", "ai"])
    parser.add_argument("--approach", default="direct", choices=["direct", "valentino"])
    parser.add_argument("--output", default=None)
    parser.add_argument("--limit", type=int, default=None)
    args = parser.parse_args()

    missing = [
        name for name, val in [
            ("AZURE_API_KEY", API_KEY),
            ("AZURE_OPENAI_ENDPOINT", OPENAI_ENDPOINT),
            ("AZURE_OPENAI_API_VERSION", OPENAI_API_VERSION),
            ("AZURE_AI_ENDPOINT", AZURE_AI_ENDPOINT),
            ("COQC_PATH", COQC_PATH),
            ("COQ_TIMEOUT", COQ_TIMEOUT),
            ("MAX_RETRIES", MAX_RETRIES),
        ] if not val
    ]
    if missing:
        print(f"ERROR: missing required env vars: {', '.join(missing)}")
        print("  copy .env.example to .env and fill in values")
        sys.exit(1)

    items = load_fracas(args.data) if args.data.endswith(".xml") else json.load(open(args.data))
    if args.limit:
        items = items[:args.limit]

    print(f"Loaded {len(items)} items, Model: {args.model}, Approach: {args.approach}\n")

    client = get_azure_client() if args.client == "azure" else get_ai_client()
    output = args.output or f"results/coq_{args.approach}_{args.model}_{len(items)}items.json"
    run_batch(items, client, args.model, approach=args.approach, output_file=output)
