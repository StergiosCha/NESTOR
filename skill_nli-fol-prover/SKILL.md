---
name: nli-fol-prover
description: >
  Translate natural language premise-hypothesis pairs into first-order logic
  and verify entailment/contradiction using automated theorem provers
  (Prover9, Mace4, E Prover). Supports SNLI/MultiNLI/SICK/FraCaS-style
  inputs. The LLM translates NL to FOL, Prover9 attempts proof (entailment),
  Mace4 searches for countermodels (non-entailment), and E Prover provides
  a fast backup. Reports proved/refuted/timeout with full proof traces.
  Trigger on: "NLI", "natural language inference", "entailment", "premise
  hypothesis", "theorem prover", "FOL", "first-order logic", "Prover9",
  "prove entailment", "FraCaS", "monotonicity", "logical form".
metadata:
  openclaw:
    emoji: "🔬"
    requires:
      bins: [python3, prover9, mace4, eprover]
---

# NLI→FOL Theorem Prover

Translate premise-hypothesis pairs to first-order logic, then prove or
refute entailment using automated theorem provers.

## Quick Use

```
Prove: "Every linguist reads a paper" entails "Some linguist reads a paper"
```

or:

```python
python3 scripts/prove.py --premise "All cats are animals" --hypothesis "Some cats are animals"
```

or with a dataset:

```python
python3 scripts/prove.py --file examples/fracas.jsonl
```

## Pipeline

```
NL pair → LLM translates to FOL → Prover9 (proof) + Mace4 (countermodel) → verdict
```

1. **LLM Translation**: Claude translates P and H into Prover9-format FOL
   with consistent predicate naming and proper quantifier scoping
2. **Prover9**: Tries to prove H from P (timeout 10s). Success = entailment.
3. **Mace4**: Tries to find a model of P ∧ ¬H (timeout 10s). Success = non-entailment.
4. **E Prover**: Backup prover using TPTP format for cross-validation.
5. **Verdict**: proved/countermodel/timeout → entailment/contradiction/neutral

## FOL Translation Conventions

The LLM is prompted to follow these conventions:

- Predicates: lowercase, descriptive (`cat(x)`, `read(x,y)`, `tall(x)`)
- Constants: lowercase (`john`, `mary`, `london`)
- Variables: `x`, `y`, `z`, `u`, `v`, `w`
- Quantifiers: `all x`, `exists x` (Prover9 syntax)
- Connectives: `->` (implies), `&` (and), `|` (or), `-` (not), `<->` (iff)
- Equality: `=`, `!=`
- Every entity gets a sort predicate where useful
- Generics/bare plurals: default to universal (`all x (cat(x) -> ...)`)
- Definites: existential + unique (`exists x (king(x) & ...`)
- Plurals: existential unless clearly universal

## Input Formats

### Single pair:
```bash
python3 scripts/prove.py -p "All dogs bark" -h "Some dogs bark"
```

### JSONL file:
```json
{"premise": "All dogs bark", "hypothesis": "Some dogs bark", "label": "entailment"}
{"premise": "No cat barks", "hypothesis": "Some cat barks", "label": "contradiction"}
```

### FraCaS XML (auto-detected):
```bash
python3 scripts/prove.py --file examples/fracas.jsonl
```

## Output

For each pair, the skill produces:
- The FOL translation (Prover9 format)
- The TPTP translation (E Prover format)
- Prover9 result: PROVED / FAILED / TIMEOUT
- Mace4 result: MODEL FOUND / FAILED / TIMEOUT
- E Prover result: Theorem / CounterSatisfiable / Timeout
- Final verdict: ENTAILMENT / CONTRADICTION / NEUTRAL
- Proof trace (if proved)
- Countermodel (if found)

## Dependencies

- `prover9` and `mace4` (LADR suite) — FOL prover + model finder
- `eprover` — E Theorem Prover (TPTP format)
- Python 3.8+
- Claude API (for NL→FOL translation, or use interactively)

## Files

- `scripts/prove.py` — Main pipeline script
- `scripts/nl_to_fol.py` — NL→FOL translation module
- `scripts/run_prover.py` — Prover9/Mace4/E wrapper
- `examples/fracas.jsonl` — Classic FraCaS test suite pairs
- `examples/basic.jsonl` — Simple test cases

## Accuracy Notes

The bottleneck is the NL→FOL translation, not the provers. Known issues:
- Generics are hard (your research area — GEN operator)
- Implicatures vs entailments (scalar, etc.)
- Presupposition projection
- Plurals and collectivity
- Intensional contexts (believe, want)

The provers themselves are sound and complete for FOL. If the translation
is correct, the proof is guaranteed correct.
