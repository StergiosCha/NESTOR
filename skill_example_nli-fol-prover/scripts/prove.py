#!/usr/bin/env python3
"""
NLI→FOL Theorem Prover Pipeline
Translate premise-hypothesis pairs to FOL and prove/refute entailment.

Usage:
  python3 prove.py -p "All cats are animals" -h "Some cats are animals"
  python3 prove.py --file examples/basic.jsonl
  python3 prove.py --fol-only -p "All dogs bark" -h "Fido barks"
"""

import argparse, json, os, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from nl_to_fol import translate
from run_prover import prove_entailment, run_prover9, run_mace4, run_eprover


def process_pair(premise: str, hypothesis: str, label: str = None,
                 api_key: str = None, timeout: int = 10,
                 fol_only: bool = False, verbose: bool = True) -> dict:
    """Process a single P/H pair through the full pipeline."""

    if verbose:
        print(f"\n{'━'*60}")
        print(f"  P: {premise}")
        print(f"  H: {hypothesis}")
        if label:
            print(f"  Gold: {label}")
        print(f"{'━'*60}")

    # Step 1: Translate to FOL
    use_llm = bool(api_key)
    fol = translate(premise, hypothesis, api_key=api_key, use_llm=use_llm)

    if verbose:
        print(f"\n  ┌─ FOL Translation ({'LLM' if use_llm else 'rule-based'}):")
        for p in fol['premises']:
            print(f"  │  Premise: {p}")
        print(f"  │  Goal:    {fol['hypothesis']}")
        if fol.get('predicates'):
            print(f"  │  Preds:   {fol['predicates']}")
        if fol.get('notes'):
            print(f"  │  Notes:   {fol['notes']}")
        print(f"  └─")

    if fol_only:
        return {'fol': fol, 'verdict': 'fol_only'}

    # Check for unparsed formulas
    if any('UNPARSED' in p for p in fol['premises']) or 'UNPARSED' in fol['hypothesis']:
        if verbose:
            print(f"\n  ⚠ Translation incomplete — skipping provers")
        return {'fol': fol, 'verdict': 'translation_failed'}

    # Step 2: Run provers
    if verbose:
        print(f"\n  Running provers (timeout={timeout}s)...")

    result = prove_entailment(fol['premises'], fol['hypothesis'], timeout=timeout)

    # Display results
    if verbose:
        p9 = result['results'].get('prover9', {})
        m4 = result['results'].get('mace4', {})
        ep = result['results'].get('eprover', {})
        p9n = result['results'].get('prover9_neg', {})

        icons = {'proved':'✓','failed':'✗','timeout':'⏱','model_found':'📋','refuted':'✗'}

        print(f"\n  ┌─ Results:")
        print(f"  │  Prover9 (P⊢H):  {icons.get(p9.get('status',''),'?')} {p9.get('status','')}"
              + (f" ({p9.get('time',0):.2f}s)" if p9.get('time') else ""))
        print(f"  │  Mace4 (P∧¬H):   {icons.get(m4.get('status',''),'?')} {m4.get('status','')}")
        print(f"  │  Prover9 (P⊢¬H): {icons.get(p9n.get('status',''),'?')} {p9n.get('status','')}")
        print(f"  │  E Prover:       {icons.get(ep.get('status',''),'?')} {ep.get('status','')} (SZS: {ep.get('szs','')})")
        print(f"  └─")

        verdict_icons = {'entailment':'✅','contradiction':'❌','neutral':'➖','unknown':'❓'}
        print(f"\n  {verdict_icons.get(result['verdict'],'?')} VERDICT: {result['verdict'].upper()}")
        print(f"  Reason: {result['reason']}")

        # Show proof if available
        if p9.get('proof'):
            print(f"\n  ┌─ Proof trace (Prover9):")
            for line in p9['proof'].split('\n')[:20]:
                if line.strip():
                    print(f"  │  {line}")
            print(f"  └─")

        # Show countermodel if available
        if m4.get('model'):
            print(f"\n  ┌─ Countermodel (Mace4):")
            for line in m4['model'].split('\n')[:15]:
                if line.strip():
                    print(f"  │  {line}")
            print(f"  └─")

    result['fol'] = fol
    result['premise'] = premise
    result['hypothesis'] = hypothesis
    result['gold_label'] = label
    result['correct'] = (label and result['verdict'] == label)

    return result


def main():
    parser = argparse.ArgumentParser(description="NLI→FOL Theorem Prover", add_help=False)
    parser.add_argument('--help', action='help', help='Show help')
    parser.add_argument('-p', '--premise', type=str, help='Premise sentence')
    parser.add_argument('-h', '--hypothesis', type=str, help='Hypothesis sentence')
    parser.add_argument('-f', '--file', type=str, help='JSONL file with pairs')
    parser.add_argument('-t', '--timeout', type=int, default=10, help='Prover timeout (seconds)')
    parser.add_argument('--fol-only', action='store_true', help='Only translate, skip provers')
    parser.add_argument('--api-key', type=str, default=os.environ.get('ANTHROPIC_API_KEY'),
                        help='Anthropic API key for LLM translation')
    parser.add_argument('-q', '--quiet', action='store_true', help='Minimal output')
    parser.add_argument('--json', action='store_true', help='Output as JSON')
    args = parser.parse_args()

    results = []

    if args.premise and args.hypothesis:
        # Single pair
        r = process_pair(args.premise, args.hypothesis,
                        api_key=args.api_key, timeout=args.timeout,
                        fol_only=args.fol_only, verbose=not args.quiet)
        results.append(r)

    elif args.file:
        # Batch from file
        with open(args.file) as f:
            pairs = [json.loads(line) for line in f if line.strip()]

        correct = total = 0
        for pair in pairs:
            r = process_pair(
                pair['premise'], pair['hypothesis'],
                label=pair.get('label'),
                api_key=args.api_key, timeout=args.timeout,
                fol_only=args.fol_only, verbose=not args.quiet
            )
            results.append(r)
            if r.get('gold_label'):
                total += 1
                if r.get('correct'):
                    correct += 1

        if total > 0:
            print(f"\n{'═'*60}")
            print(f"  Accuracy: {correct}/{total} ({correct/total*100:.1f}%)")
            print(f"{'═'*60}")

    else:
        parser.print_help()
        return

    if args.json:
        # Clean results for JSON output
        clean = []
        for r in results:
            clean.append({
                'premise': r.get('premise'),
                'hypothesis': r.get('hypothesis'),
                'verdict': r.get('verdict'),
                'gold_label': r.get('gold_label'),
                'correct': r.get('correct'),
                'fol_premises': r.get('fol', {}).get('premises'),
                'fol_hypothesis': r.get('fol', {}).get('hypothesis'),
            })
        print(json.dumps(clean, indent=2))


if __name__ == "__main__":
    main()
