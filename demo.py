#!/usr/bin/env python3
"""
NESTOR Demo — See the full pipeline in 5 minutes
=================================================
Runs 5 FraCaS items through: NL → FOL → Prover9/Mace4 → verdict

Before running:
  1. Make sure prover9 and mace4 are installed (run: prover9 --version)
  2. Set your API key: export AZURE_API_KEY="your-key"
     OR: export ANTHROPIC_API_KEY="your-key"

Usage:
  python3 demo.py              # uses LLM for translation
  python3 demo.py --no-llm     # uses rule-based translation (no API key needed)
"""

import subprocess, tempfile, os, sys, json, re, time, argparse

# ═══════════════════════════════════════════════════════════════
# 5 demo items — hand-picked to show different phenomena
# ═══════════════════════════════════════════════════════════════

DEMO_ITEMS = [
    {
        "id": "FraCaS-001",
        "section": "Quantifiers",
        "premises": ["An Italian became the world manager."],
        "hypothesis": "An Italian became a manager.",
        "gold": "yes",
        "why": "Upward monotonicity: 'world manager' → 'manager' under existential."
    },
    {
        "id": "FraCaS-044",
        "section": "Quantifiers",
        "premises": ["No delegate finished the report on time."],
        "hypothesis": "Some delegate finished the report on time.",
        "gold": "no",
        "why": "Direct contradiction: 'no X' and 'some X' are contradictory quantifiers."
    },
    {
        "id": "FraCaS-047",
        "section": "Quantifiers",
        "premises": ["Every European has the right to live in Europe."],
        "hypothesis": "Every European has the right to live in Portugal.",
        "gold": "unknown",
        "why": "Portugal ⊂ Europe, but the inference goes the wrong way (downward in predicate position)."
    },
    {
        "id": "FraCaS-004",
        "section": "Quantifiers",
        "premises": ["Every Italian man wants to be a great tenor."],
        "hypothesis": "Some Italian man wants to be a great tenor.",
        "gold": "yes",
        "why": "Every → Some: universal implies existential (assuming non-empty domain)."
    },
    {
        "id": "FraCaS-009",
        "section": "Quantifiers",
        "premises": [
            "All APCOM managers have company cars.",
            "All APCOM managers are Europeans."
        ],
        "hypothesis": "Some Europeans have company cars.",
        "gold": "yes",
        "why": "Multi-premise: APCOM managers ⊆ Europeans, APCOM managers → have cars, therefore some Europeans have cars."
    },
]


# ═══════════════════════════════════════════════════════════════
# FOL Translation
# ═══════════════════════════════════════════════════════════════

FOL_SYSTEM_PROMPT = """You are a formal semanticist translating natural language to first-order logic in Prover9 syntax.

Prover9 syntax:
- Universal: all x (P(x) -> Q(x))
- Existential: exists x (P(x) & Q(x))
- Connectives: -> & | - <->
- Variables: x, y, z (lowercase)
- Constants: lowercase (john, mary)
- Predicates: lowercase (cat, run)
- NO period at end of formulas

Conventions:
- "All/Every A are B" → all x (A(x) -> B(x))
- "Some/A A are B" → exists x (A(x) & B(x))
- "No A is B" → all x (A(x) -> -B(x))
- Bare plurals/generics → universal
- Add existential presupposition when needed

CRITICAL: When translating multiple premises, use CONSISTENT predicate names across all formulas.
If premise 1 uses "european(x)", premise 2 must use "european(x)" too, not "is_european(x)".

Return ONLY valid JSON:
{
  "premises": ["formula1", "formula2"],
  "hypothesis": "formula",
  "predicates": {"name": "meaning"},
  "notes": "brief note"
}"""


def translate_with_azure(premises, hypothesis):
    """Translate using Azure OpenAI."""
    api_key = os.environ.get("AZURE_API_KEY", "")
    endpoint = os.environ.get("AZURE_OPENAI_ENDPOINT",
        "https://kafouroutsos-8905-resource.cognitiveservices.azure.com/")
    deployment = os.environ.get("AZURE_DEPLOYMENT", "gpt-4o")
    api_version = "2024-12-01-preview"

    p_text = "\n".join(f"Premise {i+1}: {p}" for i, p in enumerate(premises))
    prompt = f"{p_text}\nHypothesis: {hypothesis}\n\nTranslate to FOL."

    url = f"{endpoint}openai/deployments/{deployment}/chat/completions?api-version={api_version}"

    import urllib.request
    body = json.dumps({
        "messages": [
            {"role": "system", "content": FOL_SYSTEM_PROMPT},
            {"role": "user", "content": prompt}
        ],
        "max_tokens": 1024,
        "temperature": 0.0,
    }).encode()

    headers = {"api-key": api_key, "Content-Type": "application/json"}
    req = urllib.request.Request(url, data=body, headers=headers)
    resp = urllib.request.urlopen(req, timeout=60)
    data = json.loads(resp.read().decode())
    text = data["choices"][0]["message"]["content"].strip()
    text = re.sub(r'^```(?:json)?\s*', '', text)
    text = re.sub(r'\s*```$', '', text)
    return json.loads(text)


def translate_with_anthropic(premises, hypothesis):
    """Translate using Anthropic API."""
    api_key = os.environ.get("ANTHROPIC_API_KEY", "")

    p_text = "\n".join(f"Premise {i+1}: {p}" for i, p in enumerate(premises))
    prompt = f"{p_text}\nHypothesis: {hypothesis}\n\nTranslate to FOL."

    import urllib.request
    body = json.dumps({
        "model": "claude-sonnet-4-20250514",
        "max_tokens": 1024,
        "system": FOL_SYSTEM_PROMPT,
        "messages": [{"role": "user", "content": prompt}]
    }).encode()

    headers = {
        "Content-Type": "application/json",
        "x-api-key": api_key,
        "anthropic-version": "2023-06-01"
    }

    req = urllib.request.Request("https://api.anthropic.com/v1/messages", data=body, headers=headers)
    resp = urllib.request.urlopen(req, timeout=60)
    data = json.loads(resp.read().decode())
    text = data["content"][0]["text"].strip()
    text = re.sub(r'^```(?:json)?\s*', '', text)
    text = re.sub(r'\s*```$', '', text)
    return json.loads(text)


def translate_rule_based(premises, hypothesis):
    """Simple pattern-matching fallback (no API needed)."""
    def parse(s):
        s = s.strip().rstrip('.')
        sl = s.lower()
        m = re.match(r'(?:all|every)\s+(\w+)s?\s+(?:are|is|have|has)\s+(.+)', sl)
        if m:
            subj = m.group(1)
            pred = re.sub(r'\s+', '_', m.group(2).strip())
            return f"all x ({subj}(x) -> {pred}(x))"
        m = re.match(r'(?:some|an?)\s+(\w+)\s+(\w+)', sl)
        if m:
            subj, pred = m.group(1), m.group(2)
            return f"exists x ({subj}(x) & {pred}(x))"
        m = re.match(r'no\s+(\w+)\s+(\w+)', sl)
        if m:
            subj, pred = m.group(1), m.group(2)
            return f"all x ({subj}(x) -> -{pred}(x))"
        return f"% UNPARSED: {s}"

    return {
        "premises": [parse(p) for p in premises],
        "hypothesis": parse(hypothesis),
        "predicates": {},
        "notes": "Rule-based (limited)"
    }


def translate(premises, hypothesis, use_llm=True):
    """Route to the right translator."""
    if use_llm:
        if os.environ.get("AZURE_API_KEY"):
            return translate_with_azure(premises, hypothesis)
        elif os.environ.get("ANTHROPIC_API_KEY"):
            return translate_with_anthropic(premises, hypothesis)
        else:
            print("    ⚠ No API key found, using rule-based translation")
            return translate_rule_based(premises, hypothesis)
    return translate_rule_based(premises, hypothesis)


# ═══════════════════════════════════════════════════════════════
# Prover Calls
# ═══════════════════════════════════════════════════════════════

def run_prover9(assumptions, goal, timeout=10):
    """Try to prove goal from assumptions. Returns (status, proof_text)."""
    input_text = "formulas(assumptions).\n"
    for a in assumptions:
        input_text += f"  {a}.\n"
    input_text += "end_of_list.\n\n"
    input_text += "formulas(goals).\n"
    input_text += f"  {goal}.\n"
    input_text += "end_of_list.\n"

    with tempfile.NamedTemporaryFile(mode='w', suffix='.in', delete=False) as f:
        f.write(input_text)
        infile = f.name

    try:
        result = subprocess.run(
            ['prover9', '-f', infile],
            capture_output=True, text=True, timeout=timeout
        )
        output = result.stdout + result.stderr
        if 'THEOREM PROVED' in output:
            proof_start = output.find('============================== PROOF')
            proof_end = output.find('============================== end of proof')
            proof = output[proof_start:proof_end] if proof_start >= 0 else ""
            return 'PROVED', proof
        return 'FAILED', output[-300:]
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', ''
    except FileNotFoundError:
        return 'NOT_INSTALLED', 'prover9 not found in PATH'
    finally:
        os.unlink(infile)


def run_mace4(assumptions, goal, timeout=10):
    """Search for countermodel (P true, H false). Returns (status, model_text)."""
    input_text = "assign(domain_size, 10).\n\n"
    input_text += "formulas(assumptions).\n"
    for a in assumptions:
        input_text += f"  {a}.\n"
    input_text += "end_of_list.\n\n"
    input_text += "formulas(goals).\n"
    input_text += f"  {goal}.\n"
    input_text += "end_of_list.\n"

    with tempfile.NamedTemporaryFile(mode='w', suffix='.in', delete=False) as f:
        f.write(input_text)
        infile = f.name

    try:
        result = subprocess.run(
            ['mace4', '-f', infile],
            capture_output=True, text=True, timeout=timeout
        )
        output = result.stdout + result.stderr
        if 'end of model' in output:
            model_start = output.find('============================== MODEL')
            model_end = output.find('============================== end of model')
            model = output[model_start:model_end+45] if model_start >= 0 else ""
            return 'COUNTERMODEL', model
        return 'FAILED', ''
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', ''
    except FileNotFoundError:
        return 'NOT_INSTALLED', 'mace4 not found in PATH'
    finally:
        os.unlink(infile)


def decide_verdict(p9_status, p9_neg_status, m4_status):
    """Combine prover results into a verdict."""
    if p9_status == 'PROVED':
        return 'ENTAILMENT'
    if p9_neg_status == 'PROVED':
        return 'CONTRADICTION'
    if m4_status == 'COUNTERMODEL':
        return 'NEUTRAL'
    return 'UNKNOWN'


# ═══════════════════════════════════════════════════════════════
# Main Demo
# ═══════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(description="NESTOR Demo")
    parser.add_argument('--no-llm', action='store_true', help='Use rule-based translation (no API key needed)')
    args = parser.parse_args()

    use_llm = not args.no_llm

    print()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║           NESTOR Demo — NLI → FOL → Theorem Prover         ║")
    print("╠══════════════════════════════════════════════════════════════╣")
    print("║  5 FraCaS items · Quantifier section · Full pipeline       ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    # Check provers
    print("\n  Checking tools...")
    for tool in ['prover9', 'mace4']:
        try:
            subprocess.run([tool], stdin=subprocess.DEVNULL, capture_output=True, timeout=2)
            print(f"    ✓ {tool} found")
        except FileNotFoundError:
            print(f"    ✗ {tool} NOT FOUND — install it first (see install_guide.docx)")
            sys.exit(1)

    if use_llm:
        if os.environ.get("AZURE_API_KEY"):
            print(f"    ✓ Azure API key found")
        elif os.environ.get("ANTHROPIC_API_KEY"):
            print(f"    ✓ Anthropic API key found")
        else:
            print(f"    ⚠ No API key — falling back to rule-based translation")
            print(f"      (Set AZURE_API_KEY or ANTHROPIC_API_KEY for LLM translation)")
            use_llm = False

    correct = 0
    total = len(DEMO_ITEMS)
    results = []

    for i, item in enumerate(DEMO_ITEMS):
        print(f"\n{'━'*64}")
        print(f"  [{i+1}/{total}] {item['id']} — {item['section']}")
        print(f"{'━'*64}")

        # Show the NL input
        for j, p in enumerate(item['premises']):
            print(f"  Premise {j+1}:   {p}")
        print(f"  Hypothesis:  {item['hypothesis']}")
        print(f"  Gold answer: {item['gold']}")
        print(f"  Why:         {item['why']}")

        # Step 1: Translate to FOL
        print(f"\n  ┌─ STEP 1: Translate to FOL", end="")
        if use_llm:
            print(" (LLM)")
        else:
            print(" (rule-based)")

        try:
            fol = translate(item['premises'], item['hypothesis'], use_llm=use_llm)
        except Exception as e:
            print(f"  │  ✗ Translation failed: {e}")
            print(f"  │    Falling back to rule-based...")
            fol = translate_rule_based(item['premises'], item['hypothesis'])

        for j, fp in enumerate(fol['premises']):
            print(f"  │  P{j+1}: {fp}")
        print(f"  │  H:  {fol['hypothesis']}")
        if fol.get('notes'):
            print(f"  │  Notes: {fol['notes']}")
        print(f"  └─")

        # Check for unparsed
        all_formulas = fol['premises'] + [fol['hypothesis']]
        if any('UNPARSED' in f for f in all_formulas):
            print(f"\n  ⚠ Translation incomplete — skipping provers")
            results.append({'verdict': 'TRANSLATION_FAILED', 'correct': False})
            continue

        # Step 2: Run provers
        print(f"\n  ┌─ STEP 2: Run provers (10s timeout each)")

        # Prover9: try P ⊢ H
        p9_status, p9_proof = run_prover9(fol['premises'], fol['hypothesis'])
        icon = {'PROVED': '✓', 'FAILED': '✗', 'TIMEOUT': '⏱', 'NOT_INSTALLED': '!'}
        print(f"  │  Prover9 (P ⊢ H):   {icon.get(p9_status, '?')} {p9_status}")

        # Mace4: try to find countermodel
        m4_status, m4_model = run_mace4(fol['premises'], fol['hypothesis'])
        icon_m = {'COUNTERMODEL': '📋', 'FAILED': '✗', 'TIMEOUT': '⏱', 'NOT_INSTALLED': '!'}
        print(f"  │  Mace4   (P ∧ ¬H):  {icon_m.get(m4_status, '?')} {m4_status}")

        # Prover9: try P ⊢ ¬H (contradiction check)
        neg_h = f"-({fol['hypothesis']})"
        p9n_status, p9n_proof = run_prover9(fol['premises'], neg_h)
        print(f"  │  Prover9 (P ⊢ ¬H):  {icon.get(p9n_status, '?')} {p9n_status}")
        print(f"  └─")

        # Step 3: Verdict
        verdict = decide_verdict(p9_status, p9n_status, m4_status)
        gold_map = {'yes': 'ENTAILMENT', 'no': 'CONTRADICTION', 'unknown': 'NEUTRAL'}
        is_correct = verdict == gold_map.get(item['gold'], '')

        verdict_icon = {'ENTAILMENT': '✅', 'CONTRADICTION': '❌', 'NEUTRAL': '➖', 'UNKNOWN': '❓'}
        print(f"\n  ┌─ STEP 3: Verdict")
        print(f"  │  {verdict_icon.get(verdict, '?')} VERDICT: {verdict}")
        print(f"  │  Gold:              {gold_map.get(item['gold'], item['gold'])}")
        print(f"  │  {'✓ CORRECT' if is_correct else '✗ WRONG'}")
        print(f"  └─")

        if is_correct:
            correct += 1

        # Show proof trace if available
        if p9_proof and p9_status == 'PROVED':
            print(f"\n  ┌─ Proof trace (Prover9):")
            for line in p9_proof.split('\n')[:15]:
                if line.strip():
                    print(f"  │  {line}")
            print(f"  └─")

        if m4_model and m4_status == 'COUNTERMODEL':
            print(f"\n  ┌─ Countermodel (Mace4):")
            for line in m4_model.split('\n')[:10]:
                if line.strip():
                    print(f"  │  {line}")
            print(f"  └─")

        results.append({'verdict': verdict, 'correct': is_correct})

    # Summary
    print(f"\n{'═'*64}")
    print(f"  SUMMARY: {correct}/{total} correct ({correct/total*100:.0f}%)")
    print(f"{'═'*64}")

    for i, (item, r) in enumerate(zip(DEMO_ITEMS, results)):
        icon = '✓' if r['correct'] else '✗'
        print(f"  {icon} {item['id']}: gold={item['gold']}, pred={r['verdict']}")

    print(f"\n  What you just saw:")
    print(f"  1. Natural language premises + hypothesis")
    print(f"  2. LLM translated them to first-order logic (Prover9 syntax)")
    print(f"  3. Prover9 tried to PROVE the hypothesis from the premises")
    print(f"  4. Mace4 tried to find a COUNTERMODEL (premises true, hypothesis false)")
    print(f"  5. Combined results → entailment / contradiction / neutral")
    print(f"\n  This is Phase 2 of NESTOR. Your job: make this work on ALL of FraCaS.")
    print()


if __name__ == "__main__":
    main()
