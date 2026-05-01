#!/usr/bin/env python3
"""
FraCaS Test Suite Evaluation via Azure AI Foundry
==================================================
Tests LLMs on the FraCaS natural language inference benchmark.
Each model produces: (1) an answer (yes/no/unknown), (2) an explanation
identifying the formal semantics phenomenon responsible for the inference.

Azure setup:
    - All models deployed as serverless endpoints under one Azure AI resource
    - OpenAI models use AzureOpenAI SDK (cognitiveservices endpoint)
    - Non-OpenAI models (DeepSeek, Llama, Mistral) use the Azure AI inference endpoint

Usage:
    export AZURE_API_KEY="your-key-here"
    python fracas_eval_azure.py [--resume] [--section N] [--model MODEL_KEY]

Results saved to: fracas_results_azure.json + fracas_summary_azure.txt
"""

import os
import sys
import json
import time
import re
import random
import argparse
import threading
from pathlib import Path
from urllib.request import urlretrieve
from urllib.error import URLError
from concurrent.futures import ThreadPoolExecutor, as_completed

from dotenv import load_dotenv

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from clients.azure import get_azure_client, get_ai_client, call_llm
from utils.fracas import load_rich, SECTIONS as FRACAS_SECTIONS

load_dotenv()

LLM_RATE_LIMIT = float(os.environ.get("LLM_RATE_LIMIT", "0") or 0)
PHASE1_MAX_TOKENS = 1024

# Model registry: each model has a deployment name and a provider type
# provider: "azure-openai" uses the OpenAI-compatible endpoint
#           "azure-ai" uses the Azure AI model inference endpoint
MODELS = {
    "gpt-4o": {
        "deployment": "gpt-4o",
        "provider": "azure-openai",
    },
    # Uncomment these as you deploy them:
    # "deepseek-r1": {
    #     "deployment": "DeepSeek-R1",
    #     "provider": "azure-ai",
    # },
    # "llama-70b": {
    #     "deployment": "Llama-3.3-70B-Instruct",
    #     "provider": "azure-ai",
    # },
    # "llama-8b": {
    #     "deployment": "Llama-3.1-8B-Instruct",
    #     "provider": "azure-ai",
    # },
    # "claude-sonnet": {
    #     "deployment": "Claude-Sonnet-4.6",
    #     "provider": "azure-ai",
    # },
}

FRACAS_XML_URL = os.environ.get("FRACAS_XML_URL", "")
FRACAS_XML_PATH = Path("fracas.xml")
RESULTS_PATH = Path("fracas_results_azure.json")
SUMMARY_PATH = Path("fracas_summary_azure.txt")

# ── FraCaS Loader ──────────────────────────────────────────────

def download_fracas():
    """Download FraCaS XML if not present."""
    if FRACAS_XML_PATH.exists():
        print(f"  FraCaS XML found at {FRACAS_XML_PATH}")
        return
    print(f"  Downloading FraCaS XML from {FRACAS_XML_URL}...")
    try:
        urlretrieve(FRACAS_XML_URL, FRACAS_XML_PATH)
        print(f"  Saved to {FRACAS_XML_PATH}")
    except URLError as e:
        print(f"  ERROR: Could not download FraCaS XML: {e}")
        sys.exit(1)


# ── Prompt Construction ────────────────────────────────────────

SYSTEM_PROMPT = """You are an expert in formal semantics and natural language inference (NLI).

Given one or more premises and a hypothesis, determine whether the hypothesis follows from the premises.

Your response MUST follow this exact format:

ANSWER: <yes|no|unknown>
PHENOMENON: <name of the formal semantics phenomenon>
EXPLANATION: <1-3 sentences explaining WHY this answer follows, referencing the specific formal semantics mechanism (e.g., downward monotonicity, scope ambiguity, privative adjective, VP ellipsis resolution, de dicto reading, distributive vs collective, temporal aspect, etc.)>

Rules:
- "yes" = the hypothesis necessarily follows from the premises
- "no" = the hypothesis is necessarily false given the premises
- "unknown" = the premises do not determine the truth of the hypothesis
- Be precise about the formal semantics phenomenon. Use standard terminology from formal semantics (Montague grammar, GQ theory, DRT, event semantics, type-logical grammar, etc.)
- Do NOT hedge. Give exactly one of: yes, no, unknown."""


def build_user_prompt(problem: dict) -> str:
    """Build the user message for a FraCaS problem."""
    parts = []
    for i, p in enumerate(problem["premises"], 1):
        parts.append(f"Premise {i}: {p}")
    parts.append(f"Hypothesis: {problem['hypothesis']}")
    return "\n".join(parts)


# ── Answer Extraction ──────────────────────────────────────────

def extract_answer(response: str) -> str:
    """Extract the answer (yes/no/unknown) from model response."""
    m = re.search(r"ANSWER:\s*(yes|no|unknown)", response, re.IGNORECASE)
    if m:
        return m.group(1).lower()

    response_lower = response.lower().strip()
    for pattern in [
        r"^(yes|no|unknown)\b",
        r"the answer is\s*(yes|no|unknown)",
        r"answer:\s*(yes|no|unknown)",
        r"\b(yes|no|unknown)\s*[.\n]",
    ]:
        m = re.search(pattern, response_lower)
        if m:
            return m.group(1)

    return "parse_error"


def extract_phenomenon(response: str) -> str:
    m = re.search(r"PHENOMENON:\s*(.+?)(?:\n|$)", response, re.IGNORECASE)
    return m.group(1).strip() if m else ""


def extract_explanation(response: str) -> str:
    m = re.search(r"EXPLANATION:\s*(.+?)(?:\n\n|$)", response, re.IGNORECASE | re.DOTALL)
    return m.group(1).strip() if m else ""


# ── Main Evaluation Loop ──────────────────────────────────────

_results_lock = threading.Lock()
_print_lock = threading.Lock()


def _safe_print(msg: str):
    with _print_lock:
        print(msg, flush=True)


def evaluate(problems: list[dict], model_key: str, model_config: dict, results: dict) -> dict:
    """Run evaluation for one model on all problems."""
    with _results_lock:
        if model_key not in results:
            results[model_key] = {}

    provider = model_config["provider"]
    client = get_azure_client() if provider == "azure-openai" else get_ai_client()
    deployment = model_config["deployment"]

    total = len(problems)
    done = len(results.get(model_key, {}))
    _safe_print(f"\n{'='*60}")
    _safe_print(f"  Model: {model_key} (deployment: {deployment})")
    _safe_print(f"  Provider: {model_config['provider']}")
    _safe_print(f"  Problems: {total} total, {done} already done")
    _safe_print(f"{'='*60}")

    completed = 0
    for i, prob in enumerate(problems):
        pid = str(prob["id"])

        with _results_lock:
            if pid in results[model_key]:
                completed += 1
                continue

        messages = [
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": build_user_prompt(prob)},
        ]

        response = call_llm(client, deployment, messages, max_tokens=PHASE1_MAX_TOKENS)
        answer = extract_answer(response)
        phenomenon = extract_phenomenon(response)
        explanation = extract_explanation(response)

        correct = answer == prob["gold"]

        entry = {
            "gold": prob["gold"],
            "predicted": answer,
            "correct": correct,
            "section": prob["section"],
            "section_name": prob["section_name"],
            "phenomenon": phenomenon,
            "explanation": explanation,
            "raw_response": response,
        }

        with _results_lock:
            results[model_key][pid] = entry
            completed += 1

        status = "✓" if correct else "✗"
        _safe_print(f"  [{model_key}] {completed}/{total}  #{pid} {status}  gold={prob['gold']}  pred={answer}  [{prob['section_name'][:30]}]")

        if completed % 5 == 0:
            with _results_lock:
                save_results(results)

        time.sleep(LLM_RATE_LIMIT)

    with _results_lock:
        save_results(results)
    return results


def evaluate_parallel(problems: list[dict], models_to_run: dict, results: dict) -> dict:
    """Run all models in parallel."""
    _safe_print(f"\n  Launching {len(models_to_run)} models in parallel...")
    _safe_print(f"  Models: {', '.join(models_to_run.keys())}")
    _safe_print(f"  Problems per model: {len(problems)}")
    _safe_print("")

    with ThreadPoolExecutor(max_workers=len(models_to_run)) as executor:
        futures = {}
        for model_key, model_config in models_to_run.items():
            future = executor.submit(evaluate, problems, model_key, model_config, results)
            futures[future] = model_key

        for future in as_completed(futures):
            model_key = futures[future]
            try:
                future.result()
                _safe_print(f"\n  ✓ {model_key} DONE")
            except Exception as e:
                _safe_print(f"\n  ✗ {model_key} FAILED: {e}")

    return results


# ── Results & Summary ──────────────────────────────────────────

def save_results(results: dict):
    with open(RESULTS_PATH, "w") as f:
        json.dump(results, f, indent=2, ensure_ascii=False)


def load_results() -> dict:
    if RESULTS_PATH.exists():
        with open(RESULTS_PATH) as f:
            return json.load(f)
    return {}


def compute_summary(results: dict, problems: list[dict]) -> str:
    lines = []
    lines.append("=" * 80)
    lines.append("FraCaS NLI Evaluation — Azure AI — Summary")
    lines.append("=" * 80)
    lines.append("")

    lines.append("OVERALL ACCURACY")
    lines.append("-" * 60)
    header = f"{'Model':<20}"
    for sec in range(1, 10):
        header += f"  S{sec:d}"
    header += "  | Overall"
    lines.append(header)
    lines.append("-" * 60)

    for model_key in MODELS:
        if model_key not in results:
            continue
        model_results = results[model_key]

        section_correct = {}
        section_total = {}
        total_correct = 0
        total_count = 0

        for pid, r in model_results.items():
            sec = r["section"]
            if sec not in section_correct:
                section_correct[sec] = 0
                section_total[sec] = 0
            if r["correct"]:
                section_correct[sec] += 1
                total_correct += 1
            section_total[sec] += 1
            total_count += 1

        row = f"{model_key:<20}"
        for sec in range(1, 10):
            if sec in section_total and section_total[sec] > 0:
                acc = section_correct.get(sec, 0) / section_total[sec] * 100
                row += f" {acc:4.0f}"
            else:
                row += "    -"
        overall = total_correct / total_count * 100 if total_count > 0 else 0
        row += f"  | {overall:5.1f}%  ({total_correct}/{total_count})"
        lines.append(row)

    lines.append("-" * 60)
    lines.append("")

    lines.append("SECTION KEY")
    for sec, name in FRACAS_SECTIONS.items():
        lines.append(f"  S{sec}: {name}")
    lines.append("")

    lines.append("DETAILED SECTION BREAKDOWN")
    lines.append("-" * 60)
    for sec in range(1, 10):
        lines.append(f"\n  S{sec}: {FRACAS_SECTIONS[sec]}")
        lines.append(f"  {'Model':<20} {'Correct':>8} {'Total':>6} {'Accuracy':>9}")
        for model_key in MODELS:
            if model_key not in results:
                continue
            model_results = results[model_key]
            correct = sum(1 for r in model_results.values() if r["section"] == sec and r["correct"])
            total = sum(1 for r in model_results.values() if r["section"] == sec)
            if total > 0:
                acc = correct / total * 100
                lines.append(f"  {model_key:<20} {correct:>8} {total:>6} {acc:>8.1f}%")

    lines.append("")

    lines.append("PARSE ERROR RATES")
    lines.append("-" * 60)
    for model_key in MODELS:
        if model_key not in results:
            continue
        model_results = results[model_key]
        errors = sum(1 for r in model_results.values() if r["predicted"] == "parse_error")
        total = len(model_results)
        if total > 0:
            lines.append(f"  {model_key:<20} {errors}/{total} ({errors/total*100:.1f}%)")

    lines.append("")

    lines.append("GOLD LABEL DISTRIBUTION")
    lines.append("-" * 60)
    gold_counts = {"yes": 0, "no": 0, "unknown": 0}
    for p in problems:
        gold_counts[p["gold"]] += 1
    for label, count in gold_counts.items():
        lines.append(f"  {label:<10} {count:>4} ({count/len(problems)*100:.1f}%)")

    lines.append("")

    lines.append("TOP PHENOMENA IDENTIFIED (per model, top 10)")
    lines.append("-" * 60)
    for model_key in MODELS:
        if model_key not in results:
            continue
        model_results = results[model_key]
        phenom_counts = {}
        for r in model_results.values():
            p = r.get("phenomenon", "").strip()
            if p:
                phenom_counts[p] = phenom_counts.get(p, 0) + 1
        if phenom_counts:
            lines.append(f"\n  {model_key}:")
            sorted_p = sorted(phenom_counts.items(), key=lambda x: -x[1])[:10]
            for name, count in sorted_p:
                lines.append(f"    {count:>3}x  {name}")

    lines.append("")
    lines.append("=" * 80)

    return "\n".join(lines)


# ── Balanced Sampling ──────────────────────────────────────────

def balanced_sample(problems: list[dict], n_per_label: int = 20, seed: int = 42) -> list[dict]:
    rng = random.Random(seed)

    by_label = {"yes": [], "no": [], "unknown": []}
    for p in problems:
        by_label[p["gold"]].append(p)

    sampled = []
    for label in ["yes", "no", "unknown"]:
        pool = by_label[label]
        if len(pool) <= n_per_label:
            sampled.extend(pool)
            print(f"  WARNING: only {len(pool)} '{label}' problems available (requested {n_per_label})")
        else:
            by_sec = {}
            for p in pool:
                by_sec.setdefault(p["section"], []).append(p)
            for sec in by_sec:
                rng.shuffle(by_sec[sec])

            picked = []
            sec_keys = sorted(by_sec.keys())
            idx = {s: 0 for s in sec_keys}
            while len(picked) < n_per_label:
                added_this_round = False
                for s in sec_keys:
                    if len(picked) >= n_per_label:
                        break
                    if idx[s] < len(by_sec[s]):
                        picked.append(by_sec[s][idx[s]])
                        idx[s] += 1
                        added_this_round = True
                if not added_this_round:
                    break
            sampled.extend(picked)

    rng.shuffle(sampled)
    return sampled


# ── CLI ────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="FraCaS NLI evaluation via Azure AI")
    parser.add_argument("--resume", action="store_true", help="Resume from existing results")
    parser.add_argument("--section", type=int, default=0, help="Run only section N (1-9), 0=all")
    parser.add_argument("--model", type=str, default="", help="Run only this model key")
    parser.add_argument("--summary-only", action="store_true", help="Just print summary")
    parser.add_argument("--single-premise-only", action="store_true",
                        help="Only test single-premise problems")
    parser.add_argument("--balanced", type=int, default=0, metavar="N",
                        help="Sample N problems per label for balanced eval")
    parser.add_argument("--seed", type=int, default=42, help="Random seed (default: 42)")
    parser.add_argument("--parallel", action="store_true",
                        help="Run all models in parallel")
    args = parser.parse_args()

    if not args.summary_only:
        missing = [
            name for name, val in [
                ("AZURE_API_KEY", os.environ.get("AZURE_API_KEY", "")),
                ("AZURE_OPENAI_ENDPOINT", os.environ.get("AZURE_OPENAI_ENDPOINT", "")),
                ("AZURE_OPENAI_API_VERSION", os.environ.get("AZURE_OPENAI_API_VERSION", "")),
                ("AZURE_AI_ENDPOINT", os.environ.get("AZURE_AI_ENDPOINT", "")),
                ("FRACAS_XML_URL", FRACAS_XML_URL),
            ] if not val
        ]
        if missing:
            print(f"ERROR: missing required env vars: {', '.join(missing)}")
            print("  copy .env.example to .env and fill in values")
            sys.exit(1)

    # Load FraCaS
    print("Loading FraCaS test suite...")
    download_fracas()
    problems = load_rich(FRACAS_XML_PATH)
    print(f"  Parsed {len(problems)} problems across {len(set(p['section'] for p in problems))} sections")

    if args.single_premise_only:
        problems = [p for p in problems if len(p["premises"]) == 1]
        print(f"  Filtered to {len(problems)} single-premise problems")

    if args.section > 0:
        problems = [p for p in problems if p["section"] == args.section]
        print(f"  Filtered to section {args.section}: {len(problems)} problems")

    if args.balanced > 0:
        problems = balanced_sample(problems, n_per_label=args.balanced, seed=args.seed)
        from collections import Counter
        dist = Counter(p["gold"] for p in problems)
        print(f"  Balanced sample: {len(problems)} problems ({dict(dist)})")

    results = load_results() if args.resume or args.summary_only else {}

    if args.summary_only:
        summary = compute_summary(results, problems)
        print(summary)
        with open(SUMMARY_PATH, "w") as f:
            f.write(summary)
        print(f"\nSummary saved to {SUMMARY_PATH}")
        return

    models_to_run = MODELS
    if args.model:
        if args.model not in MODELS:
            print(f"ERROR: Unknown model key '{args.model}'. Available: {', '.join(MODELS.keys())}")
            sys.exit(1)
        models_to_run = {args.model: MODELS[args.model]}

    if args.parallel and len(models_to_run) > 1:
        results = evaluate_parallel(problems, models_to_run, results)
    else:
        for model_key, model_config in models_to_run.items():
            results = evaluate(problems, model_key, model_config, results)

    summary = compute_summary(results, problems)
    print(summary)
    with open(SUMMARY_PATH, "w") as f:
        f.write(summary)
    print(f"\nResults saved to {RESULTS_PATH}")
    print(f"Summary saved to {SUMMARY_PATH}")


if __name__ == "__main__":
    main()
