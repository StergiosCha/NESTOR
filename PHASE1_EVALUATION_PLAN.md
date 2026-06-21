# Phase 1 Explanation Evaluation — Student Plan

## What You Have

180 result files in `phase1_nli_eval/results/`, structured as:

```
{dataset}__{model}__{technique}__{language}.json
```

### Datasets (5)

| Dataset | Items | Language | Notes |
|---------|-------|----------|-------|
| fracas | 342 | English | Original FraCaS |
| fracas-translated | 342 | Greek | FraCaS translated to Greek |
| fracas-extended | 427 | Greek | Extended Greek FraCaS |
| fracas-multilabel | 713 | Greek | Multi-label variant |
| oyxoy | 1,049 | Greek | OYXOY-NLI |

### Models (9)

gpt-4o, gpt-5.4, deepseek-r1, deepseek-v4-pro, grok-4-20, grok-4-20-reasoning, llama-3.3-70b, llama-4-maverick, mistral-large-3

### Conditions

- **Technique:** zero-shot, few-shot
- **Language:** el (Greek prompt), en (English prompt)

### File structure

Each JSON has `metadata`, `results`, `summary`. Each item in `results` has:
- `id`, `premise`, `hypothesis`, `tags` (gold phenomenon), `fracas_sections`
- `gold` (gold label list), `predicted` (predicted label list)
- `reasoning` (the model's explanation — THIS is what you evaluate)
- `success`, `partial_success`

---

## What You Need To Do

Two things: (A) LLM-as-judge scoring, (B) 10% human validation.

---

## A. LLM-as-Judge

### Scope

Evaluate ALL files with explanations. That's:

- 5 datasets × 9 models × 2 techniques × 2 languages = 180 files
- Total explanations: ~(342 + 342 + 427 + 713 + 1049) × 9 × 2 × 2 ≈ **103,000**

**Start with zero-shot EL only** (the core condition): 5 datasets × 9 models = 45 files ≈ **25,830 explanations**. Extend to other conditions after validation passes.

### Judge prompt

Send each explanation to GPT-4o (temperature 0):

```
You are an expert evaluator of NLI explanations.

Given:
- Premise: {premise}
- Hypothesis: {hypothesis}
- Gold label: {gold}
- Gold phenomenon tags: {tags}
- Model's predicted label: {predicted}
- Model's explanation: {reasoning}

Score the explanation on three criteria. Output ONLY a JSON object.

1. phenomenon_id (0/1/2):
   2 = explanation correctly identifies the phenomenon matching the gold tags
   1 = explanation addresses a related but incorrect phenomenon
   0 = explanation is generic, circular, or identifies an irrelevant phenomenon

2. soundness (0/1/2):
   2 = reasoning is logically valid and linguistically accurate
   1 = reasoning has minor errors but overall direction is correct
   0 = reasoning is wrong, contradictory, or incoherent

3. consistency (0/1):
   1 = explanation supports the predicted label (regardless of correctness)
   0 = explanation contradicts or is unrelated to the predicted label

Output: {"phenomenon_id": X, "soundness": X, "consistency": X}
```

### Implementation steps

1. Write a script `evaluate_explanations.py` that:
   - Takes `--dataset`, `--model`, `--technique`, `--language` as arguments
   - Loads the corresponding result file
   - Loops over all items, sends each to GPT-4o via Azure
   - Parses the JSON scores
   - Saves to `results/judge_scores/{dataset}__{model}__{technique}__{language}__scores.json`

2. Run the zero-shot EL condition first (45 files)

3. Each scored file should contain:
```json
{
  "metadata": { "dataset": "...", "model": "...", "judge": "gpt-4o", ... },
  "scores": [
    {
      "id": "oyxoy-0002",
      "gold": ["Contradiction"],
      "predicted": ["Contradiction"],
      "tags": ["Lexical Entailment:FAO"],
      "phenomenon_id": 2,
      "soundness": 2,
      "consistency": 1,
      "total": 5
    }
  ]
}
```

### Compute (per file)

- Mean total score (max 5)
- Mean per criterion
- % phenomenon_id = 2 (correct identification)
- % "right for wrong reasons": success == 1 AND phenomenon_id == 0
- Breakdown by `tags` / `fracas_sections`

---

## B. Human Validation (10%)

### Sample selection

Per dataset, randomly sample 10% of items. Use seed 42 for reproducibility.

| Dataset | Items | 10% sample | × 9 models | Explanations to score |
|---------|-------|------------|------------|----------------------|
| fracas | 342 | 34 | 306 | 306 |
| fracas-translated | 342 | 34 | 306 | 306 |
| fracas-extended | 427 | 43 | 387 | 387 |
| fracas-multilabel | 713 | 71 | 639 | 639 |
| oyxoy | 1,049 | 105 | 945 | 945 |
| **Total** | | **287** | | **2,583** |

**Practical shortcut:** If 2,583 is too many, validate on zero-shot EL only = 287 items × 9 models = **2,583** → still large. Alternative: validate 10% of items × 3 representative models (gpt-4o, deepseek-r1, llama-3.3-70b) = **861 explanations**. Discuss with Stergios.

```python
import random
random.seed(42)
# Per dataset:
sample_ids = random.sample(item_ids, len(item_ids) // 10)
```

Save sample IDs to `results/judge_scores/human_validation_samples.json`.

### Annotation

Two annotators independently score using the same 3-criterion rubric. Use a spreadsheet:

```
item_id | model | premise | hypothesis | gold | predicted | tags | reasoning | phenomenon_id | soundness | consistency
```

Do NOT discuss scores until both annotators are done.

### Agreement (Cohen's κ)

```python
from sklearn.metrics import cohen_kappa_score

# Per criterion, compute 3 kappas:
kappa_human = cohen_kappa_score(ann1, ann2)        # inter-annotator
kappa_judge_a1 = cohen_kappa_score(judge, ann1)    # judge vs annotator 1
kappa_judge_a2 = cohen_kappa_score(judge, ann2)    # judge vs annotator 2
```

Compute separately for phenomenon_id, soundness, consistency.
Report per dataset.

### Decision rule

- κ(judge, humans) ≥ 0.7 on all three criteria → LLM judge scores stand
- κ < 0.7 on any criterion → fall back to full human annotation for that criterion

---

## Deliverables

1. `results/judge_scores/` — one scored JSON per input file (start with 45 zero-shot EL files)
2. `results/judge_scores/human_validation_samples.json` — sampled item IDs per dataset
3. `results/judge_scores/human_scores_ann1.csv` + `human_scores_ann2.csv`
4. `results/judge_scores/agreement_report.txt` — all κ values
5. Summary tables:
   - Per model × dataset: mean scores, right-for-wrong-reasons %
   - Per phenomenon × model: heatmap of phenomenon_id
   - Cross-lingual comparison (el vs en prompt): paired scores per model on fracas/fracas-translated

## Priority order

1. Build `evaluate_explanations.py`
2. Run on **oyxoy zero-shot el** + **fracas zero-shot en** (the two core datasets)
3. Human validation on those two
4. If κ ≥ 0.7, run remaining conditions
5. Summary tables and heatmaps
