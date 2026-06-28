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
from typing import Callable

from dotenv import load_dotenv
from rich.progress import BarColumn, MofNCompleteColumn, Progress, SpinnerColumn, TextColumn, TimeElapsedColumn

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from clients.azure import assert_env, call_llm, get_client
from clients.models import MODELS
from data.loaders import load_dataset
from data.schema import Sample
from phase2_fol.prompts import PROMPT_TIER, build_correction_prompt, build_prompt

load_dotenv()

PROVER9_PATH = os.environ.get("PROVER9_PATH", "")
MACE4_PATH = os.environ.get("MACE4_PATH", "")
PROVER_TIMEOUT = int(os.environ.get("PROVER_TIMEOUT", "30") or 30)

MAX_RETRIES = int(os.environ.get("MAX_RETRIES", "3") or 3)

FOL_MAX_TOKENS = 500
FLUSH_EVERY = 10

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


ERROR_MARKERS = ("error", "fatal", "%%")


def trim_prover_error(output: str, max_lines: int = 10, max_chars: int = 1000) -> str:
    """Reduce a Prover9/MACE4 dump to the salient error line(s)."""

    if not output:
        return output
    lines = output.splitlines()
    keep: list[str] = []
    for i, line in enumerate(lines):
        if any(m in line.lower() for m in ERROR_MARKERS):
            keep.append(line.strip())
            nxt = lines[i + 1].strip() if i + 1 < len(lines) else ""
            if nxt and not any(m in nxt.lower() for m in ERROR_MARKERS):
                keep.append(nxt)
    if not keep:
        return output.strip()[-max_chars:]
    return "\n".join(keep[:max_lines])[:max_chars]


# ============================================================
# VERIFICATION LOOP (Phase 3)
# ============================================================

def fix_fol(client, model, premise, hypothesis, previous_fol, error_message):
    """Ask LLM to fix FOL based on error feedback."""
    messages = build_correction_prompt(premise, hypothesis, previous_fol, error_message)
    return call_llm(client, model, messages, max_tokens=FOL_MAX_TOKENS)


STEPS = ("entailment_proved", "contradiction_proved",
              "entailment_refuted", "contradiction_refuted")


def build_fol_result(premises, hyp, label, steps, attempt, errors, raw) -> dict:
    """Assemble run_fol_pipeline's return dict: three-way label + 4-boolean steps_detail."""
    return {
        "fol_premises": premises,
        "fol_hypothesis": hyp,
        "label": label,
        "steps_detail": steps,
        "attempts": attempt,
        "errors": errors,
        "raw_fol": raw,
    }


def run_fol_pipeline(client, model, sample: Sample, dataset, max_retries=None,
                     condition="c1"):
    """Full pipeline with verification loop for one Sample.

    The prompt is chosen by state, not by attempt number: we send the correction
    prompt (fol_fix) only when a previous translation exists to correct. An LLM
    transport failure leaves no translation, so the next attempt re-runs nl_to_fol.

    Once a translation parses and passes the syntax check, the four-phase verdict
    (Prover9 P⊢H and P⊢¬H; MACE4 P∧¬H and P∧H) runs once and returns — only
    LLM/parse/syntax errors re-enter the retry loop.

    Returns the core FOL result dict:
        - fol_premises, fol_hypothesis: final FOL
        - label: "Entailment" / "Contradiction" / "Unknown" / "Undecided"
        - steps_detail: the four prover booleans (see STEPS)
        - attempts: number of attempts used
        - errors: list of error messages from failed attempts
        - raw_fol: last LLM output (debugging); "<LLM call failed: ...>" on API error
    """
    max_retries = max_retries or MAX_RETRIES
    premise, hypothesis = sample.premise, sample.hypothesis
    gold_label = ", ".join(sample.labels)
    errors = []
    raw = ""
    premises, hyp = [], None
    has_translation = False  # True once we hold raw FOL text to correct

    for attempt in range(1, max_retries + 1):
        # Step 1: translate, or correct a previous translation if we have one.
        try:
            if not has_translation:
                raw = translate_to_fol(client, model, premise, hypothesis,
                                       condition=condition, gold_label=gold_label,
                                       item_id=sample.id, dataset=dataset)
            else:
                raw = fix_fol(client, model, premise, hypothesis, raw, errors[-1])
        except Exception as e:
            errors.append(f"<LLM call failed: {type(e).__name__}: {e}>")
            has_translation = False  # next attempt re-translates, not corrects
            continue
        has_translation = True

        premises, hyp = parse_fol_output(raw)

        if not premises or not hyp:
            errors.append(f"Parse error: could not extract premises/hypothesis from LLM output:\n{raw}")
            continue

        # Step 2: Syntax check
        ok, err = syntax_check_fol(premises, hyp)
        if not ok:
            errors.append(f"Syntax error: {trim_prover_error(err)}")
            continue

        # Steps 3-6: four-phase verdict. neg_hyp reuses the validated hypothesis;
        # MACE4 negates its goal, so passing neg_hyp makes it search P∧H (Phase D).
        # Prover timeout yields False (no proof / no model)
        neg_hyp = f"-({hyp})"
        entailment_proved, _ = run_prover9(premises, hyp)         # Phase A: P ⊢ H
        contradiction_proved, _ = run_prover9(premises, neg_hyp)  # Phase B: P ⊢ ¬H
        entailment_refuted = contradiction_refuted = False
        if entailment_proved and contradiction_proved:
            label = "Undecided"          # inconsistent P proves both
        elif entailment_proved:
            label = "Entailment"
        elif contradiction_proved:
            label = "Contradiction"
        else:
            entailment_refuted, _ = run_mace4(premises, hyp)         # Phase C: P ∧ ¬H
            contradiction_refuted, _ = run_mace4(premises, neg_hyp)  # Phase D: P ∧ H
            label = "Unknown" if (entailment_refuted and contradiction_refuted) else "Undecided"

        steps = {
            "entailment_proved": entailment_proved,
            "contradiction_proved": contradiction_proved,
            "entailment_refuted": entailment_refuted,
            "contradiction_refuted": contradiction_refuted,
        }
        return build_fol_result(premises, hyp, label, steps, attempt, errors, raw)

    # All attempts exhausted: never reached valid FOL.
    steps = {k: False for k in STEPS}
    return build_fol_result(premises if premises else [], hyp or "", "Undecided", steps,
                       max_retries, errors, raw or (errors[-1] if errors else ""))


# ============================================================
# RESULT SHAPING
# ============================================================

def fol_entry(sample: Sample, fol_result: dict) -> dict:
    """Shape one result-file entry: Sample metadata + FOL verdict + success.

    Three-way scoring: success is a direct membership test of the pipeline label
    against the gold set (multilabel-safe). 'Undecided' is never a gold label, so
    it always scores as a failure.
    """
    gold = list(sample.labels)
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
        "label": fol_result["label"],
        "steps_detail": fol_result["steps_detail"],
        "attempts": fol_result["attempts"],
        "errors": fol_result["errors"],
        "raw_fol": fol_result["raw_fol"],
        "success": 1 if fol_result["label"] in set(gold) else 0,
    }


def _is_llm_error(entry: dict) -> bool:
    return str(entry.get("raw_fol", "")).startswith("<LLM call failed")


def summarize_results(results: list[dict]) -> dict:
    total = len(results)

    def label_count(label: str) -> int:
        return sum(1 for r in results if r["label"] == label)

    llm_error = sum(1 for r in results if _is_llm_error(r))
    success_count = sum(1 for r in results if r.get("success") == 1)
    avg_attempts = sum(r["attempts"] for r in results) / total if total else 0
    return {
        "total": total,
        "entailment": label_count("Entailment"),
        "contradiction": label_count("Contradiction"),
        "unknown": label_count("Unknown"),
        "undecided": label_count("Undecided"),
        "llm_error": llm_error,
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
            "prompt_tier": PROMPT_TIER,
            "started_at": _now_iso(),
            "completed_at": None,
        },
        "results": [],
    }


def _flush(path: Path, state: dict) -> None:
    state["summary"] = summarize_results(state["results"])
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")


def _is_complete(entry: dict) -> bool:
    """An item is done unless it errored at the LLM transport (those get retried on resume)."""
    return entry.get("label") is not None and not _is_llm_error(entry)


def run(
    dataset: str,
    model: str,
    condition: str = "c1",
    resume: bool = False,
    limit: int | None = None,
    on_progress: Callable[[], None] | None = None,
    output_file: str | None = None,
) -> int:
    """Run the FOL pipeline sequentially over one dataset x model x condition.

    Items run one at a time (each completing its full retry loop before the next),
    so a single model only ever has one in-flight LLM call. Cross-model parallelism
    lives in run_bulk; there is no per-item rate limiting here.
    """
    provider = MODELS[model]["provider"]
    assert_env(provider)
    client = get_client(model)

    samples = load_dataset(dataset)
    path = Path(output_file) if output_file else _results_path(dataset, model, condition)

    if resume and path.exists():
        state = json.loads(path.read_text(encoding="utf-8"))
        results_by_id = {e["id"]: e for e in state["results"]}
        completed = {eid for eid, e in results_by_id.items() if _is_complete(e)}
    else:
        state = _new_state(dataset, model, condition)
        results_by_id = {}
        completed = set()

    pending = [s for s in samples if s.id not in completed]
    if limit is not None:
        pending = pending[:limit]
    total, skipped = len(samples), len(samples) - len(pending)
    print(
        f"[run] dataset={dataset} model={model} condition={condition} "
        f"total={total} skipped(resume)={skipped}"
    )

    def _process(sample: Sample, progress_cb: Callable[[], None] | None) -> None:
        fol_result = run_fol_pipeline(client, model, sample, dataset, condition=condition)
        results_by_id[sample.id] = fol_entry(sample, fol_result)
        state["results"] = list(results_by_id.values())
        if len(state["results"]) % FLUSH_EVERY == 0:
            _flush(path, state)
        if progress_cb is not None:
            progress_cb()

    desc = f"  {dataset} / {model} / {condition}"
    if on_progress is not None:
        for sample in pending:
            _process(sample, on_progress)
    else:
        with Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}"),
            BarColumn(),
            MofNCompleteColumn(),
            TimeElapsedColumn(),
        ) as progress:
            task = progress.add_task(desc, total=len(pending))
            for sample in pending:
                _process(sample, lambda: progress.advance(task))

    state["results"] = list(results_by_id.values())
    state["metadata"]["completed_at"] = _now_iso()
    _flush(path, state)
    s = state["summary"]
    acc = f"{s['accuracy']:.1%}" if s["accuracy"] is not None else "n/a"
    print(
        f"[done] {s['success_count']}/{s['total']} ({acc}) | "
        f"E={s['entailment']} C={s['contradiction']} U={s['unknown']} undec={s['undecided']} "
        f"llm_error={s['llm_error']} -> {path}"
    )
    return 0


# ============================================================
# MAIN
# ============================================================

def build_parser():
    import argparse

    p = argparse.ArgumentParser(
        prog="phase2_fol.fol_pipeline",
        description="NESTOR FOL pipeline: dataset x model x condition.",
    )
    p.add_argument("-d", "--data", required=True, choices=sorted(DATASETS),
                   help="Dataset key (see data/loaders.py).")
    p.add_argument("-m", "--model", required=True, choices=sorted(MODELS),
                   help="Model key from clients.models.MODELS.")
    p.add_argument("--condition", default="c1", choices=["c1", "c2", "c3", "c4"],
                   help="c1 (blind), c2 (phase1 pred), c3 (gold), c4 (phase1+expl).")
    p.add_argument("--resume", action="store_true",
                   help="Resume an existing results file for this combination.")
    p.add_argument("--limit", type=int, default=None, metavar="N",
                   help="Process at most N pending samples.")
    p.add_argument("--output", default=None,
                   help="Output JSON file (default: results/{dataset}/{dataset}__{model}__{condition}.json).")
    return p


def main(argv=None) -> int:
    args = build_parser().parse_args(argv)
    return run(args.data, args.model, args.condition,
               resume=args.resume, limit=args.limit, output_file=args.output)


if __name__ == "__main__":
    raise SystemExit(main())
