# NESTOR — Coq Pipeline + Paper Draft

## You are working on

**NESTOR** (Neurosymbolic Evaluation of Semantic Textual Reasoning) — a project evaluating how well LLMs understand Natural Language Inference through three lenses:

1. **Phase 1 — NLI evaluation**: 9 LLMs predict entailment/contradiction/neutral on 5 NLI datasets (FraCaS variants + OYXOY-NLI), zero-shot and few-shot, in English and Greek. An LLM-as-judge (GPT-5.4) scores the quality of their explanations on 3 criteria: phenomenon identification (0/1/2), soundness (0/1/2), consistency (0/1). Human reviewers score a sample to validate the judge.

2. **Phase 2a — FOL pipeline**: LLMs translate NLI pairs to first-order logic, then Prover9/MACE4 proves or refutes entailment/contradiction. Already run — ~23,670 entries across all datasets.

3. **Phase 2b — Coq pipeline**: LLMs translate NLI pairs to Coq (higher-order, constructive logic), then `coqc` verifies the proof. **This is what needs to run.**

## Repository layout

```
NESTOR/
├── phase1_nli_eval/
│   ├── results/{dataset}/{dataset}__{model}__{technique}__{language}.json   # 180 files
│   ├── judge_scores/{dataset}/{dataset}__{model}__zero-shot__en__scores.json # 39 done
│   ├── eval_judge.py          # LLM-as-judge prompt + parser
│   ├── eval_runner.py         # batch runner with resume + concurrency
│   └── nli_pipeline.py        # Phase 1 NLI runner
├── phase2_fol/
│   ├── fol_pipeline.py        # NL → FOL → Prover9/MACE4
│   └── results/{dataset}/     # ~23,670 entries, done
├── phase2_coq/
│   ├── coq_pipeline.py        # NL → Coq → coqc (THE PIPELINE TO RUN)
│   ├── lib/                   # 5 .v files shipped with repo
│   ├── prompts/               # T0, T1, T2, T3, valentino, coq_fix
│   └── results/               # only "krikri" pilot runs (near-zero compilation)
├── coq_foundations/            # 44 hand-verified .v files (Montague, GQ, tense, aspect, mass, etc.)
├── reviews/                   # human review JSON files (690 items, 2 reviewers)
├── clients/                   # azure.py, models.py — API clients
└── data/                      # FraCaS XML + flat JSON, OYXOY
```

## Datasets

| Dataset | Items | Language | Notes |
|---------|-------|----------|-------|
| fracas | 342 | English | Original FraCaS test suite |
| fracas-translated | 342 | Greek | FraCaS translated to Greek |
| fracas-extended | 427 | Greek | Extended Greek variant |
| fracas-multilabel | 713 | Greek | Multi-label variant |
| oyxoy | 1,049 | Greek | OYXOY-NLI corpus |

FraCaS has 9 sections: §1 Quantifiers, §2 Plurals, §3 Anaphora, §4 Ellipsis, §5 Adjectives, §6 Comparatives, §7 Temporal, §8 Verbs/Attitudes, §9 Nominalization.

## Models (9)

gpt-4o, gpt-5.4, deepseek-r1, deepseek-v4-pro, grok-4-20, grok-4-20-reasoning, llama-3.3-70b, llama-4-maverick, mistral-large-3

All accessed via Azure. See `clients/models.py` for deployment names.

---

## TASK 1: Fix and run the Coq pipeline

### Current state

Student "krikri" ran all 4 tiers on FraCaS (342 items). **Result: 0–2 compilations out of 342 per tier.** The generated Coq is broken — models use `Hypothesis` (local declaration) instead of `Axiom`, produce syntax errors, wrong module references, etc.

### Experimental design — 3 configurations

Run FraCaS (342 items, English, zero-shot) with all 9 models under three prompt tiers:

| Config | Tier | What the LLM sees | Prompt file |
|--------|------|--------------------|-------------|
| A — Zero info | T0 | Syntax rules + quantifier patterns + 3 NLI examples | `prompts/nl_to_coq_T0.txt` |
| B — One example file | T1 | T0 + full `Montague.v` (140 lines) | `prompts/nl_to_coq_T1.txt` |
| C — Phenomenon-matched | T2 | T0 + section-matched .v files from `coq_foundations/` | `prompts/nl_to_coq_T2.txt` |

Condition: **C1 (blind)** — no gold label, no Phase 1 prediction. The LLM decides the relation itself.

Section → foundation file mapping (T2):
- §1 Quantifiers → Montague.v, BarwiseCooper.v
- §2 Plurals → Link1983.v, Montague.v
- §3 Anaphora → DonkeyScope.v, Montague.v
- §4 Ellipsis → Montague.v
- §5 Adjectives → AdjectivesExtension.v, MTT_base.v
- §6 Comparatives → AdjectivesExtension.v, Montague.v
- §7 Temporal → DowtyTense.v, Montague.v
- §8 Verbs/Attitudes → PTQ.v, kratzer2.v
- §9 Nominalization → MTT_base.v, Montague.v

### Prompt fixes needed BEFORE running

The prompts in `prompts/nl_to_coq_T*.txt` need these changes:

1. **Add explicit rule against `Hypothesis`:**
   After the `=== COQ SETUP ===` section, add:
   ```
   CRITICAL: Use `Axiom` or `Parameter` for premises, NEVER `Hypothesis`.
   `Hypothesis` in Coq creates a local assumption that causes compilation
   errors outside a Section. Always write:
     Axiom p1 : ...    (* for premise formalisations *)
     Parameter X : ...  (* for type/predicate declarations *)
   ```

2. **Add post-processing in `coq_pipeline.py`:**
   In `extract_coq_code()`, after extracting the code, add:
   ```python
   # Auto-fix common LLM errors
   code = re.sub(r'^Hypothesis\b', 'Axiom', code, flags=re.MULTILINE)
   ```

3. **Strip the CONDITION block for C1:**
   The code already does this (`build_coq_prompt` strips `=== CONDITION ===` for c1). Verify it works.

### How to run

```bash
cd NESTOR

# Pilot: 10 items from §1, one model, T0
python -m phase2_coq.coq_pipeline --data data/fracas/fracas.xml \
  --model gpt-4o --tier T0 --condition c1 --section 1 --limit 10 \
  --output phase2_coq/results/pilot_T0_gpt-4o_s1.json

# If pilot compilation rate > 30%, proceed to full runs:
# For each tier in T0, T1, T2:
#   For each model in the 9 models:
python -m phase2_coq.coq_pipeline --data data/fracas/fracas.xml \
  --model {MODEL} --tier {TIER} --condition c1 \
  --output phase2_coq/results/fracas__{MODEL}__T{TIER}__c1.json
```

Requirements: `coqc` (Coq 8.18+) must be in PATH. Azure API keys in `.env`.

### What to measure (per tier × model)

- **Compilation rate**: % of items where coqc returns 0
- **Proof completion rate**: % where both Qed (not Abort) on the correct theorem
- **Accuracy**: % where `extract_coq_label()` matches gold
- **Attempts distribution**: how many retries needed (max 3)
- **Error taxonomy**: syntax vs type vs tactic failure vs timeout

### Expected output structure

Each result file is a JSON list:
```json
[
  {
    "id": "fracas-0001",
    "gold": "yes",
    "predicted_label": "entailment",  // or "contradiction", "neutral", "error"
    "compiled": true,
    "proof_complete": true,
    "correct": true,
    "coq_code": "Parameter Entity : Type. ...",
    "approach": "direct",
    "attempts": 1,
    "errors": []
  }
]
```

---

## TASK 2: Run missing LLM-as-judge evaluations

### Done
- 39 files scored: fracas (10), fracas-translated (10), fracas-multilabel (9), oyxoy (10)
- All zero-shot EN, using GPT-5.4 as judge

### Missing
- **fracas-extended**: 0 files scored (should be 9–10 models × zero-shot EN)

### How to run

```bash
cd NESTOR

# Run all fracas-extended models
python -m phase1_nli_eval.eval_runner --data fracas-extended --technique zero-shot --resume

# Or one model at a time:
python -m phase1_nli_eval.eval_runner --data fracas-extended --model gpt-4o --technique zero-shot --resume
```

The runner auto-discovers result files, skips already-scored items (with `--resume`), and flushes incrementally.

---

## TASK 3: Draft the paper

### Paper structure (target: EMNLP / *SEM / LREC-COLING)

**Title**: something like "Neurosymbolic Evaluation of LLM Reasoning in Natural Language Inference: From Explanations to Formal Proofs"

### Sections

#### 1. Introduction
- LLMs achieve high NLI accuracy but do they actually reason?
- Three evaluation angles: explanation quality, FOL proofs, Coq proofs
- Contribution: the first study that evaluates NLI explanations AND attempts automated formalisation in both FOL and Coq

#### 2. Related Work
- NLI benchmarks (FraCaS, SNLI, MultiNLI, XNLI)
- LLM-as-judge evaluation (Zheng et al. 2023, etc.)
- Formal methods for NLI (Abzianidze's LangPro, Yanaka et al., Martinez-Gomez et al.)
- Neurosymbolic approaches

#### 3. Experimental Setup
- 3.1 Datasets (5 datasets, their properties, why FraCaS matters for phenomenon-level analysis)
- 3.2 Models (9 LLMs, why these — mix of proprietary/open, reasoning/non-reasoning)
- 3.3 Conditions (zero-shot/few-shot, EN/EL prompts)
- 3.4 Evaluation framework:
  - Phase 1: LLM-as-judge (3 criteria, GPT-5.4 judge, human validation)
  - Phase 2a: FOL pipeline (NL → FOL → Prover9/MACE4, 4-phase decision tree)
  - Phase 2b: Coq pipeline (NL → Coq → coqc, 3 prompt tiers T0/T1/T2)

#### 4. Results

**4.1 NLI Accuracy** (Phase 1 predictions)
- Table: model × dataset accuracy matrix
- Zero-shot vs few-shot comparison
- EN vs EL prompt comparison (cross-lingual)
- Breakdown by FraCaS section

**4.2 Explanation Quality** (LLM-as-judge + human validation)
- Table: model × dataset mean scores (phenomenon_id, soundness, consistency, total)
- "Right for wrong reasons" analysis: items where prediction is correct but phenomenon_id = 0
- Per-phenomenon heatmap: which phenomena do models explain well/poorly?
- Judge reliability: kappa(judge, human), kappa(human, human)

**4.3 FOL Formalisation** (Phase 2a)
Data already available — ~23,670 entries across all datasets:
- Table: model × dataset FOL accuracy
- Compilation/proof success rates
- Error taxonomy: 49.6% antonymy/semantic gap, 18.8% timeout, 13.7% no shared predicates, 2.7% GQ mistranslation
- Confusion matrices (predicted vs gold per label)
- Cross-lingual: EN vs EL FOL accuracy

**4.4 Coq Formalisation** (Phase 2b — from Task 1 above)
- Table: model × tier compilation rate, proof rate, accuracy
- T0 vs T1 vs T2 comparison — does formal context help?
- Error analysis: why Coq fails where FOL succeeds
- Qualitative examples of successful/failed proofs

**4.5 Cross-pipeline Comparison**
- Items that Phase 1 gets right but FOL/Coq gets wrong (and vice versa)
- Does explanation quality (Phase 1 scores) predict formalisation success?
- Correlation: phenomenon_id score ↔ FOL accuracy ↔ Coq compilation

#### 5. Discussion
- The "formalisability gap": models can explain but can't formalise
- Antonymy wall in FOL (49.6% of errors)
- Constructive vs classical logic: what Coq reveals that Prover9 doesn't
- Implications for neurosymbolic NLI

#### 6. Conclusion

### Data to compute for the paper

All values must be **computed dynamically from result files**, never hardcoded.

**From Phase 1 results** (`phase1_nli_eval/results/`):
- Accuracy per model × dataset × technique × language
- Confusion matrices
- Per-section breakdown

**From judge scores** (`phase1_nli_eval/judge_scores/`):
- Mean phenomenon_id, soundness, consistency per model × dataset
- "Right for wrong reasons" rate
- Per-phenomenon-tag heatmap

**From human reviews** (`reviews/`):
- Cohen's kappa(judge, human) per criterion
- Cohen's kappa(human, human) per criterion (where 2 reviewers overlap)

**From FOL results** (`phase2_fol/results/`):
- Each file has: `metadata`, `results` (list), `summary`
- Each result item has: `success` (bool), `label` (predicted), `gold`, `steps_detail` (4 booleans: entailment_proved, contradiction_proved, entailment_refuted, contradiction_refuted), `errors`, `tags`, `fracas_sections`

**From Coq results** (`phase2_coq/results/` — after Task 1):
- Each file is a JSON list of items with: `compiled`, `proof_complete`, `predicted_label`, `correct`, `attempts`, `errors`

### Key analysis scripts to write

1. `analysis/phase1_tables.py` — accuracy tables, confusion matrices
2. `analysis/judge_analysis.py` — explanation quality tables, heatmaps, right-for-wrong-reasons
3. `analysis/fol_analysis.py` — FOL accuracy, error taxonomy, cross-lingual
4. `analysis/coq_analysis.py` — compilation/proof rates per tier × model
5. `analysis/cross_pipeline.py` — correlations between Phase 1 scores, FOL accuracy, Coq success
6. `analysis/agreement.py` — kappa computation from human reviews vs judge scores

---

## Important constraints

- **All numbers must be computed from actual data files.** Never hardcode a result.
- **FraCaS sections** are encoded in item IDs: `fracas-{section}-{number}` (e.g., `fracas-1-023` = §1 Quantifiers, item 23).
- **Gold labels** vary by dataset: FraCaS uses `yes/no/unknown/undef`, OYXOY uses `Entailment/Contradiction/Neutral`. Normalise before comparing.
- **The FOL pipeline decision tree**: Phase A: Prover9 P⊢H → entailment. Phase B: Prover9 P⊢¬H → contradiction. Phase C: MACE4 P∧¬H sat? Phase D: MACE4 P∧H sat? Both C+D satisfied → Unknown. Neither → Undecided.
- **Azure API**: all models are accessed through `clients/azure.py`. Check `.env` for keys.
- **Coq must be installed locally** (`coqc` in PATH, version 8.18+). It is NOT available in this VM.
