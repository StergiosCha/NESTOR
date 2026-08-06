# Human Evaluation Plan — 400 Items, 20 Annotators

## Overview

We have 103,000 NLI explanations scored automatically by an LLM judge (GPT-4o). We need humans to evaluate a representative sample for two purposes: (1) human evaluation data for the paper, (2) verification that the LLM judge is reliable (Cohen's kappa >= 0.7).

## Rubric (same as the judge)

Each explanation is scored on 3 criteria:

- **Phenomenon identification** (0/1/2): Does the explanation correctly identify the linguistic phenomenon?
- **Soundness** (0/1/2): Is the reasoning logically valid and linguistically accurate?
- **Consistency** (0/1): Does the explanation support the predicted label?

Max total: 5 points per explanation.

## Sample Design

### Size: 400 items

400 items × 2 annotators each = 800 annotations / 20 people = **40 per person** (~2 hours of work).

### Stratification

Items are sampled to ensure representation across all experimental dimensions:

| Dataset | Pool size | Sample | Per model | Per technique |
|---------|-----------|--------|-----------|---------------|
| fracas | 342 | 60 | ~7 | ~3 ZS + ~4 FS |
| fracas-translated | 342 | 60 | ~7 | ~3 ZS + ~4 FS |
| fracas-extended | 427 | 70 | ~8 | 4 ZS + 4 FS |
| fracas-multilabel | 713 | 90 | ~10 | 5 ZS + 5 FS |
| oyxoy | 1,049 | 120 | ~13 | 6-7 ZS + 6-7 FS |
| **Total** | | **400** | | |

### Sampling constraints

1. Every model appears at least 3 times per dataset
2. ~50/50 zero-shot vs few-shot
3. Every FraCaS section represented at least twice
4. 60% correct / 40% wrong predictions (oversampling failures — that's where explanation quality matters most)
5. Seed 42 for reproducibility

## Annotation Setup

### Pairing: 10 pairs × 40 items

- 20 annotators form 10 pairs
- Each pair shares the same 40 items
- No overlap between pairs — every item is scored exactly twice
- This gives 10 independent kappa estimates

### Assignment

| Pair | Annotators | Items |
|------|------------|-------|
| 1 | A1, A2 | items 1–40 |
| 2 | A3, A4 | items 41–80 |
| 3 | A5, A6 | items 81–120 |
| ... | ... | ... |
| 10 | A19, A20 | items 361–400 |

### Rules

- Each annotator works independently — no discussion until both are done
- Use the Streamlit review app (`streamlit run review_app.py`) or fill in the JSON manually (see `REVIEW_APP_README.md`)
- Score all 3 criteria for every item before moving to the next

## After Annotation

### 1. Inter-annotator agreement

Per criterion, per pair:

```python
from sklearn.metrics import cohen_kappa_score
kappa = cohen_kappa_score(annotator_1_scores, annotator_2_scores)
```

Report: kappa per criterion (phenomenon_id, soundness, consistency), averaged across 10 pairs.

### 2. Judge verification

Compare each human annotator's scores with the LLM judge's scores on the same items:

```python
kappa_judge = cohen_kappa_score(judge_scores, human_scores)
```

**What we report:**
- kappa(human, human) per criterion — inter-annotator agreement
- kappa(judge, human) per criterion — judge reliability
- Mean scores per criterion, per model, per dataset from both humans and judge

### 3. What to report in the paper

- Human evaluation scores: mean per criterion, per model, per dataset
- Inter-annotator agreement: kappa per criterion
- Judge reliability: kappa(judge, human) per criterion
- If judge is validated: full results from 103,000 explanations using judge scores
- Breakdown by phenomenon tags and FraCaS sections

## Timeline

| Step | Who | When |
|------|-----|------|
| Run LLM judge on zero-shot EL (45 files) | Dev | Week 1 |
| Generate 400-item sample | Dev | Week 1 |
| Distribute items to 10 pairs | Stergios | Week 1 |
| Annotators score their 40 items | 20 annotators | Week 2 |
| Compute agreement, verify judge | Dev | Week 2 |
| If kappa OK: run judge on remaining 135 files | Dev | Week 3 |
| Summary tables and analysis | Everyone | Week 3 |
