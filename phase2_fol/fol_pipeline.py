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
from datetime import datetime, timezone
from pathlib import Path
from dotenv import load_dotenv

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from clients.azure import get_client, call_llm
from data.loaders import load_dataset
from data.schema import Sample
from phase2_fol.prompts import build_correction_prompt, build_prompt

load_dotenv()

PROVER9_PATH = os.environ.get("PROVER9_PATH", "")
MACE4_PATH = os.environ.get("MACE4_PATH", "")
PROVER_TIMEOUT = int(os.environ.get("PROVER_TIMEOUT", "30") or 30)

MAX_RETRIES = int(os.environ.get("MAX_RETRIES", "3") or 3)

FOL_MAX_TOKENS = 500

RESULTS_DIR = Path(__file__).resolve().parent / "results"
DATASETS = {"fracas", "fracas-translated", "fracas-extended", "fracas-multilabel", "oyxoy"}

# ============================================================
# PHASE 1 RESULTS (for C2/C4 conditions)
# ============================================================
# C2/C4 inject a reference model's Phase 1 prediction for the same dataset.

PHASE1_RESULTS_DIR = Path(__file__).resolve().parent.parent / "phase1_nli_eval" / "results"
PHASE1_SOURCE_TECHNIQUE = "zero-shot"

_phase1_cache: dict[tuple[str, str], dict] = {}


def _phase1_path(dataset: str, model: str = "gpt-4o") -> Path:
    name = f"{dataset}__{model}__{PHASE1_SOURCE_TECHNIQUE}__en.json"
    return PHASE1_RESULTS_DIR / dataset / name


def load_phase1_results(dataset: str, model: str = "gpt-4o") -> dict:
    """Load the reference Phase 1 result file for *dataset*/*model*, keyed by sample id (cached)."""
    key = (dataset, model)
    if key not in _phase1_cache:
        path = _phase1_path(dataset, model)
        if path.exists():
            state = json.loads(path.read_text(encoding="utf-8"))
            _phase1_cache[key] = {e["id"]: e for e in state.get("results", [])}
        else:
            print(f"WARNING: Phase 1 results not found at {path}")
            _phase1_cache[key] = {}
    return _phase1_cache[key]


def get_phase1_prediction(item_id, dataset):
    """Get the reference Phase 1 prediction and reasoning for an item (best-effort)."""
    entry = load_phase1_results(dataset).get(item_id, {})
    predicted = entry.get("predicted")
    return {
        "label": predicted if predicted else "unknown",
        "explanation": entry.get("reasoning", ""),
    }


# ============================================================
# FOL TRANSLATION
# ============================================================

def translate_to_fol(client, model, premise, hypothesis,
                     condition="c1", gold_label=None, item_id=None, dataset=None):
    """Ask LLM to translate P, H into FOL (Prover9 syntax, fixed F1 tier)."""
    phase1_label = ""
    phase1_explanation = ""
    if condition in ("c2", "c4") and item_id and dataset:
        p1 = get_phase1_prediction(item_id, dataset)
        phase1_label = p1["label"]
        phase1_explanation = p1["explanation"]
    messages = build_prompt(
        condition, premise, hypothesis,
        gold_label=gold_label or "",
        phase1_label=phase1_label,
        phase1_explanation=phase1_explanation,
    )
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
    messages = build_correction_prompt(premise, hypothesis, previous_fol, error_message)
    return call_llm(client, model, messages, max_tokens=FOL_MAX_TOKENS)


def run_fol_pipeline(client, model, sample: Sample, dataset, max_retries=None,
                     condition="c1"):
    """Full pipeline with verification loop for one Sample.

    Returns the core FOL result dict:
        - fol_premises, fol_hypothesis: final FOL
        - proved, countermodel: prover results
        - label: "entailment" / "non-entailment" / "unknown"
        - attempts: number of attempts used
        - errors: list of error messages from failed attempts
        - raw_fol: last LLM output (debugging)
    """
    max_retries = max_retries or MAX_RETRIES
    premise, hypothesis = sample.premise, sample.hypothesis
    gold_label = ", ".join(sample.labels)
    errors = []
    raw = ""
    premises, hyp = [], None

    for attempt in range(1, max_retries + 1):
        # Step 1: Get FOL translation
        if attempt == 1:
            raw = translate_to_fol(client, model, premise, hypothesis,
                                   condition=condition, gold_label=gold_label,
                                   item_id=sample.id, dataset=dataset)
        else:
            raw = fix_fol(client, model, premise, hypothesis,
                         raw, errors[-1])

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
        "errors": errors, "raw_fol": raw,
    }


# ============================================================
# RESULT SHAPING
# ============================================================

def fol_entry(sample: Sample, fol_result: dict) -> dict:
    """Shape one result-file entry: Sample metadata + FOL result + success.

    Correctness is a collapsed-gold binary projection: FOL distinguishes only
    entailment vs. not, so success compares "did FOL prove entailment?" against
    "is Entailment in the gold set?". Contradiction and Unknown both count as
    non-entailment (see the Phase 2 FOL doc warning).
    """
    gold = list(sample.labels)
    gold_entails = "Entailment" in set(gold)
    fol_entails = fol_result["label"] == "entailment"
    return {
        "id": sample.id,
        "source": sample.source,
        "language": sample.language,
        "premise": sample.premise,
        "hypothesis": sample.hypothesis,
        "tags": list(sample.tags),
        "fracas_sections": list(sample.fracas_sections),
        "gold": gold,
        "fol_premises": fol_result["fol_premises"],
        "fol_hypothesis": fol_result["fol_hypothesis"],
        "proved": fol_result["proved"],
        "countermodel": fol_result["countermodel"],
        "label": fol_result["label"],
        "attempts": fol_result["attempts"],
        "errors": fol_result["errors"],
        "raw_fol": fol_result["raw_fol"],
        "success": 1 if fol_entails == gold_entails else 0,
    }


def summarize_results(results: list[dict]) -> dict:
    total = len(results)
    proved = sum(1 for r in results if r["proved"])
    countermodel = sum(1 for r in results if r["countermodel"])
    unknown = sum(1 for r in results if r["label"] == "unknown")
    success_count = sum(1 for r in results if r.get("success") == 1)
    avg_attempts = sum(r["attempts"] for r in results) / total if total else 0
    return {
        "total": total,
        "proved": proved,
        "countermodel": countermodel,
        "unknown": unknown,
        "success_count": success_count,
        "accuracy": success_count / total if total else None,
        "avg_attempts": avg_attempts,
    }


# ============================================================
# BATCH RUNNER
# ============================================================

def _now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _results_path(dataset: str, model: str, condition: str) -> Path:
    return RESULTS_DIR / dataset / f"{dataset}__{model}__{condition}.json"


def _new_state(dataset: str, model: str, condition: str) -> dict:
    return {
        "metadata": {
            "dataset": dataset,
            "model": model,
            "condition": condition,
            "prompt_tier": "F1",
            "started_at": _now_iso(),
            "completed_at": None,
        },
        "results": [],
    }


def _flush(path: Path, state: dict) -> None:
    state["summary"] = summarize_results(state["results"])
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")


def run_batch(samples, client, model, dataset, condition="c1", output_file=None):
    """Run the FOL pipeline over a list of Samples and write a result state file."""
    path = Path(output_file) if output_file else _results_path(dataset, model, condition)
    state = _new_state(dataset, model, condition)

    for i, sample in enumerate(samples):
        print(f"[{i+1}/{len(samples)}] {sample.id}: ", end="", flush=True)
        fol_result = run_fol_pipeline(client, model, sample, dataset, condition=condition)
        entry = fol_entry(sample, fol_result)
        state["results"].append(entry)
        status = "✓" if entry["success"] else "✗"
        print(f"{entry['label']} (attempt {entry['attempts']}) {status}")

    state["metadata"]["completed_at"] = _now_iso()
    _flush(path, state)

    s = state["summary"]
    print(f"\n--- Summary ({dataset} / {model} / {condition}) ---")
    print(f"Total: {s['total']}")
    print(f"Proved: {s['proved']}, Countermodel: {s['countermodel']}, Unknown: {s['unknown']}")
    acc = f"{s['accuracy']:.1%}" if s["accuracy"] is not None else "n/a"
    print(f"Accuracy: {s['success_count']}/{s['total']} ({acc})")
    print(f"Avg attempts: {s['avg_attempts']:.1f}")
    print(f"Results saved to {path}")
    return state


# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="NESTOR FOL Pipeline")
    parser.add_argument("-d", "--data", required=True, choices=sorted(DATASETS),
                        help="Dataset key (see data/loaders.py)")
    parser.add_argument("-m", "--model", default="gpt-4o",
                        help="Model key (see clients/models.py)")
    parser.add_argument("--output", default=None,
                        help="Output JSON file (default: results/{dataset}__{model}__{condition}.json)")
    parser.add_argument("--limit", type=int, default=None,
                        help="Max items to process")
    parser.add_argument("--condition", default="c1", choices=["c1", "c2", "c3", "c4"],
                        help="Condition: c1 (blind), c2 (phase1 pred), c3 (gold), c4 (phase1+expl)")
    args = parser.parse_args()

    samples = load_dataset(args.data)
    if args.limit:
        samples = samples[:args.limit]

    print(f"Loaded {len(samples)} samples from {args.data}")
    print(f"Model: {args.model}, Condition: {args.condition}\n")

    client = get_client(args.model)
    run_batch(samples, client, args.model, args.data,
              condition=args.condition, output_file=args.output)
