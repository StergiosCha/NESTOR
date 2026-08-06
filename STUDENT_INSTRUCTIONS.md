# NESTOR — Student Instructions (30 May 2026)

Pull first:

    cd ~/NESTOR && git pull origin main


---

## Part A: Phase 1 — Explanation Evaluation

Phase 1 results are in `phase1_nli_eval/results/`. Each entry has: `gold`, `predicted`, `correct`, `section`, `phenomenon`, `explanation`.

Current evaluation is string-match only (predicted == gold). We need LLM-as-judge evaluation of the explanations.


### A1. Write the evaluation script

Create `phase1_nli_eval/eval_judge.py`. For every Phase 1 result entry, send the following to the judge model (GPT-4o or Claude):

**Judge prompt (English):**

```
You are an expert evaluator of Natural Language Inference explanations.

Given:
- Premise(s): {premise}
- Hypothesis: {hypothesis}
- Gold phenomenon tag: {phenomenon}
- Model's predicted label: {predicted}
- Model's explanation: {explanation}

Score the explanation on three criteria. Return valid JSON only.

1. Phenomenon Identification (0/1/2):
   2 = Explanation correctly identifies the phenomenon matching the gold tag
   1 = Explanation addresses a related but wrong phenomenon
   0 = Explanation is generic, circular, or identifies an irrelevant phenomenon

2. Soundness (0/1/2):
   2 = Reasoning is logically valid and linguistically accurate
   1 = Reasoning contains minor errors but overall direction is correct
   0 = Reasoning is wrong, contradictory, or incoherent

3. Label-Explanation Consistency (0/1):
   1 = The explanation supports the predicted label (regardless of correctness)
   0 = The explanation contradicts or is unrelated to the predicted label

Respond: {"phenomenon_id": <0|1|2>, "soundness": <0|1|2>, "consistency": <0|1>, "justification": "<brief>"}
```

**Judge prompt (Greek):**

```
Είσαι ειδικός αξιολογητής εξηγήσεων Συμπερασμού Φυσικής Γλώσσας (NLI).

Δεδομένα:
- Προκείμενη/ες: {premise}
- Υπόθεση: {hypothesis}
- Χρυσή ετικέτα φαινομένου: {phenomenon}
- Πρόβλεψη μοντέλου: {predicted}
- Εξήγηση μοντέλου: {explanation}

Βαθμολόγησε την εξήγηση σε τρία κριτήρια. Απάντησε μόνο με έγκυρο JSON.

1. Αναγνώριση Φαινομένου (0/1/2):
   2 = Η εξήγηση αναγνωρίζει σωστά το φαινόμενο που αντιστοιχεί στη χρυσή ετικέτα
   1 = Η εξήγηση αναφέρεται σε συναφές αλλά λανθασμένο φαινόμενο
   0 = Η εξήγηση είναι γενική, κυκλική ή αναγνωρίζει άσχετο φαινόμενο

2. Ορθότητα (0/1/2):
   2 = Η συλλογιστική είναι λογικά έγκυρη και γλωσσολογικά ακριβής
   1 = Η συλλογιστική περιέχει μικρά σφάλματα αλλά η γενική κατεύθυνση είναι σωστή
   0 = Η συλλογιστική είναι λανθασμένη, αντιφατική ή ασυνάρτητη

3. Συνέπεια Ετικέτας-Εξήγησης (0/1):
   1 = Η εξήγηση υποστηρίζει την προβλεπόμενη ετικέτα (ανεξαρτήτως ορθότητας)
   0 = Η εξήγηση αντιφάσκει ή δεν σχετίζεται με την προβλεπόμενη ετικέτα

Απάντηση: {"phenomenon_id": <0|1|2>, "soundness": <0|1|2>, "consistency": <0|1>, "justification": "<σύντομη>"}
```

Max score per item: 5 (2+2+1).

The script should:
- Read a Phase 1 results file (any format: `fracas_results_azure.json` or the pipeline output `fracas__gpt-4o__zero-shot__en.json`)
- Call the judge model on each entry
- Save output to `phase1_nli_eval/results/judge_{source}_{judge_model}.json`
- Use `clients.azure` for the API call (same as `nli_pipeline.py`)


### A2. Compute statistics

After the judge runs, compute per result file:
- Mean score per criterion (Phenomenon ID, Soundness, Consistency)
- Mean total score (out of 5)
- Breakdown by section and by phenomenon
- "Right for wrong reasons" rate: items where `correct=true` but `phenomenon_id=0`
- Per-model comparison table if multiple models were evaluated

Save stats to `phase1_nli_eval/results/judge_stats_{source}.json`.


### A3. Human validation (10% sample)

Two team members independently score a random 10% of the items using the same rubric. Compute:
- Cohen's kappa between the two humans
- Cohen's kappa between each human and the LLM judge
- If kappa < 0.7 between LLM judge and humans, we fall back to full human annotation

Use a simple spreadsheet or CSV for human scores. The eval script should have a `--compare-human` flag that reads the human CSV and computes kappa.


---

## Part B: Phase 2 — Formal Methods

### B1. Check Phase 1 results first

Look at `phase1_nli_eval/results/fracas_results_azure.json`. This has gpt-4o predictions on 30 FraCaS items (21/30 correct). Each entry has `gold`, `predicted`, `correct`, `section`, `phenomenon`, `explanation`.

Which sections does the LLM get wrong? Those are the interesting ones for Phase 2.

These predictions feed into conditions C2 and C4 (see below).


### B2. Prompts — read, modify, translate

**FOL prompts** (in `phase2_fol/prompts/`):

| Tier | File | Description |
|------|------|-------------|
| F0 | `nl_to_fol.txt` | Bare prompt. If you have been working on this, modify accordingly. |
| F1 | `nl_to_fol_F1.txt` | 22 translation conventions + 8 examples (same as above) |
| F2 | `nl_to_fol_F2.txt` | Davidsonian event semantics (same as above)|

**Coq prompts** (in `phase2_coq/prompts/`):

| Tier | File | Description |
|------|------|-------------|
| T0 | `nl_to_coq_T0.txt` | Syntax rules only, Montague-style |
| T1 | `nl_to_coq_T1.txt` | T0 + Montague.v foundation |
| T2 | `nl_to_coq_T2.txt` | T0 + section-matched foundation files |
| T3 | `nl_to_coq_T3.txt` | T0 + rich context, more files per section |

**What to do:**
1. Read the prompt files for the tier(s) you are working on.
2. If you have been modifying a prompt (e.g. F0), keep your modifications — do not overwrite with the repo version.
3. Create Greek versions of your prompts. Name them with `_el` suffix: `nl_to_fol_el.txt`, `nl_to_fol_F1_el.txt`, `nl_to_coq_T0_el.txt`, etc.
4. For Greek prompts: translate all instructions and examples into Greek. Keep the JSON output format keys in English (`premise`, `hypothesis`, `fol`, `coq_code`).


### B3. Conditions

Four experimental conditions control what context the LLM gets:

| Condition | What the LLM sees | Flag |
|-----------|-------------------|------|
| C1 | Nothing extra (blind) | `--condition c1` |
| C2 | Phase 1 predicted label | `--condition c2` |
| C3 | Gold label | `--condition c3` |
| C4 | Phase 1 predicted label + NL explanation | `--condition c4` |

C2 and C4 read from `phase1_nli_eval/results/fracas_results_azure.json`.


### B4. Running experiments

**FOL:**

    cd NESTOR
    python -m phase2_fol.fol_pipeline --section 1 --prompt F0 --condition c1 --model gpt-4o
    python -m phase2_fol.fol_pipeline --section 1 --prompt F1 --condition c1 --model gpt-4o
    python -m phase2_fol.fol_pipeline --section 1 --prompt F2 --condition c1 --model gpt-4o

**Coq:**

    cd NESTOR
    python -m phase2_coq.coq_pipeline --section 1 --tier T0 --condition c1 --model gpt-4o
    python -m phase2_coq.coq_pipeline --section 1 --tier T1 --condition c1 --model gpt-4o
    python -m phase2_coq.coq_pipeline --section 1 --tier T2 --condition c1 --model gpt-4o

Results go to `phase2_fol/results/` and `phase2_coq/results/`.

**Workflow:**
1. Use `--limit 5` for quick tests before full runs.
2. Run all prompt tiers on Section 1 with condition C1. Compare accuracy.
3. Pick the best tier. Run conditions C1, C2, C3, C4 on it. Compare.
4. Use `--section 1` through `--section 9` for different FraCaS sections.


### B5. Available models

See `clients/models.py`:

    gpt-4o, gpt-5.4, deepseek-r1, deepseek-v4-pro, llama-3.3-70b,
    llama-4-maverick, mistral-large-3, phi-4, grok-4-20, grok-4-20-reasoning,
    krikri-8b


---

## Common flags

    --section 1       FraCaS section (1-9)
    --limit 10        process only first N items
    --model gpt-4o    model name
    --output file.json    custom output path


## If something breaks

- Missing env vars: check `.env` has `AZURE_API_KEY` and `AZURE_OPENAI_ENDPOINT`
- prover9/mace4 not found: `which prover9`, ask Stergios
- coqc not found: `coqc --version`, should be 8.18+
