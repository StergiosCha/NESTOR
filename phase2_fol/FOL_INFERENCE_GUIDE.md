# FOL Inference Pipeline — Decision Tree

## Current state

`fol_pipeline.py` does two checks:

1. Prover9: P ⊢ H → entailment
2. MACE4: P ∧ ¬H sat → non-entailment

This misses **contradiction** (P ⊢ ¬H) and conflates non-entailment with unknown.

## What to implement

Four phases, run in order. Exit as soon as you get a definitive answer.

```
Phase A   Prover9: P ⊢ H        → PROVED → label = entailment (exit)
Phase B   Prover9: P ⊢ ¬H       → PROVED → label = contradiction (exit)
Phase C   MACE4:   P ∧ ¬H sat?  → record found_c = True/False
Phase D   MACE4:   P ∧ H  sat?  → record found_d = True/False

Decision after C+D:
  found_c AND found_d       →  unknown
  anything else             →  undecided
```

That's it. Log the `found_c` / `found_d` values alongside `undecided` for error analysis later, but the label is just `undecided`.

## What to change in `fol_pipeline.py`

### 1. `build_prover9_input` — add negation mode

Current `mode` is `"prove"` or `"counter"`. Add `"prove_neg"`:

```python
if mode == "prove_neg":
    # Negate hypothesis: put ¬H in goals
    lines.append("formulas(goals).\n")
    lines.append(f"  -({hypothesis}).\n")
    lines.append("end_of_list.\n")
```

### 2. `run_mace4` — add positive-sat mode

Current MACE4 checks P ∧ ¬H (goals = H, MACE4 negates goals internally). For Phase D you need P ∧ H. Easiest way: put H in assumptions, not goals.

```python
def run_mace4_sat(premises, hypothesis, negate_h=True, timeout=None):
    """
    negate_h=True:  check P ∧ ¬H (put H in goals — MACE4 negates it)
    negate_h=False: check P ∧ H  (put H in assumptions — MACE4 checks as-is)
    """
```

### 3. `run_fol_pipeline` — replace the current prove/counter block

```python
# Phase A: Prover9 P ⊢ H
proved_h, _ = run_prover9(premises, hyp)
if proved_h:
    return result(label="entailment")

# Phase B: Prover9 P ⊢ ¬H
proved_neg_h, _ = run_prover9_neg(premises, hyp)
if proved_neg_h:
    return result(label="contradiction")

# Phase C: MACE4 P ∧ ¬H sat?
found_c, _ = run_mace4_sat(premises, hyp, negate_h=True)

# Phase D: MACE4 P ∧ H sat?
found_d, _ = run_mace4_sat(premises, hyp, negate_h=False)

if found_c and found_d:
    return result(label="unknown")
else:
    return result(label="undecided", found_c=found_c, found_d=found_d)
```

### 4. Retries — only on parse/syntax errors

Move the retry loop so it wraps **only** steps 1–2 (LLM translation + syntax check). Once you have valid FOL, run all four phases once — retrying the same valid FOL against Prover9/MACE4 won't change anything.

```python
for attempt in range(1, max_retries + 1):
    raw = translate_to_fol(...)  # or fix_fol(...) on retry
    premises, hyp = parse_fol_output(raw)
    ok, err = syntax_check_fol(premises, hyp)
    if not ok:
        errors.append(err)
        continue  # retry translation
    break  # valid FOL, proceed to proving

# Now run phases A–D (no retry loop here)
```

## Accuracy computation

For computing accuracy against gold labels:

| Pipeline label | Matches gold `yes` | Matches gold `no` | Matches gold `unknown` |
|---|---|---|---|
| entailment | ✓ | | |
| contradiction | | ✓ | |
| unknown | | | ✓ |
| undecided | — skip from accuracy, report separately — |

Report: accuracy (excluding undecided), undecided rate, and breakdown of undecided by `found_c`/`found_d` pattern.

## Why this order

Prover9 first because proofs are definitive (universal). MACE4 second because models are existential evidence. A↔B order doesn't matter (both are Prover9 calls, independent). C↔D order doesn't matter either (both MACE4, independent — run them both regardless).
