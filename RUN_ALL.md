# RUN EVERYTHING — end to end

What to run, in order, with exact commands. Costs are computed from
measured token counts (prompt sizes from the real prompt builder; output
size 795 tok from 2,736 real generations; retry factor 1.252 from 23,670
completed FOL items) at Azure list prices.

**Total to complete every experiment: $965 (pilot $17 + Coq grid $695 + FOL c2/c3 $242 + wave 0 $10).** Do it in four waves; each
wave has a gate so you never spend the next wave's money on a broken run.

| wave | what | cost | why |
|---|---|---|---|
| **0** | fix 1 broken FOL run + backfill 2 missing cells | **$10.26** | data is currently incomplete and one file is corrupt |
| **1** | Coq pilot, 486 generations | **$7.28** | gate: does the patched prompt compile at all |
| **2** | FOL c2 + c3, all datasets | **$242.35** | completes the condition grid; pipeline already works |
| **3** | Coq full grid, 27,702 generations | **$415.72** | only if wave 1 passes its gate |
| | (optional) Coq T3 | +$309.65 | only if T2 beats T1 |

---

## Prerequisites (once)

```bash
cd /path/to/NESTOR
cp .env.example .env      # fill in:
#   AZURE_API_KEY, AZURE_OPENAI_ENDPOINT, AZURE_AI_ENDPOINT
#   LITELLM_HOST, LITELLM_ILSP_EVAL_API_KEY
#   GPT_5_4_PRO_ENDPOINT, GPT_5_4_PRO_API_KEY
```

Build the container. `coqc` must live on the same machine as the
pipeline, and the Dockerfile compiles a smoke file at build time so a
broken compiler fails the build instead of turning all 27,702 items into
identical `coqc_missing` errors.

```bash
export ACR=youracr RG=nestor-rg LOC=westeurope STORAGE=yourstorage
az group create -n "$RG" -l "$LOC"
az acr create -g "$RG" -n "$ACR" --sku Basic
az storage account create -g "$RG" -n "$STORAGE" -l "$LOC" --sku Standard_LRS
az storage share create --account-name "$STORAGE" -n nestor-results

az acr build -r "$ACR" -t nestor:latest -f deploy/Dockerfile .
```

Verify the image before spending anything:

```bash
docker run --rm --platform linux/amd64 "$ACR.azurecr.io/nestor:latest" \
  -c "import subprocess;print(subprocess.run(['coqc','--version'],capture_output=True,text=True).stdout)"
```

---

## WAVE 0 — repair the existing data ($10.26)

Two problems the audit found. Both corrupt current results, so fix them
before computing anything.

**0a. One FOL run is truncated: 2 of 713 items.**
`fracas-multilabel__deepseek-r1__c1.json` contains 2 items and reports
accuracy 0.000 over them. It is not a real result — it is why
`deepseek-r1` shows a black 0.00 cell in the FOL heatmap. Delete and rerun
($3.34):

```bash
rm phase2_fol/results/fracas-multilabel/fracas-multilabel__deepseek-r1__c1.json
python phase2_fol/fol_pipeline.py --data fracas-multilabel --model deepseek-r1 --condition c1
```

**0b. Two FOL cells were never run.** `deepseek-r1` is missing on
`fracas-extended` and `oyxoy`, so the FOL grid is 43/45 and every
per-model comparison silently drops a model on two datasets ($6.92):

```bash
for ds in fracas-extended oyxoy; do
  python phase2_fol/fol_pipeline.py --data "$ds" --model deepseek-r1 --condition c1
done
```

**Gate:** `python analysis/audit.py` must report no `truncated run` and no
`high` severity defect other than the pending Coq runs.

---

## WAVE 1 — Coq pilot, the gate that protects $415.72 ($7.28)

486 generations: 3 tiers × 2 conditions × 3 models × 27 items. The sample
is **stratified** — 3 items from each of the 9 FraCaS sections. A plain
`--limit 27` would give 27 items of section 1 only and tell you nothing
about the other eight phenomena.

```bash
export AZURE_API_KEY=... AZURE_OPENAI_ENDPOINT=...
MODELS="gpt-5.4 grok-4-20-reasoning llama-3.3-70b" \
TIERS="T0 T1 T2" CONDS="c1 c3" \
EXTRA="--stratified 3 --seed 0" \
bash deploy/azure_fanout.sh          # 18 containers, ~10 min

az storage file download-batch --account-name "$STORAGE" \
   -s nestor-results -d phase2_coq/results
python analysis/coq_analysis.py
```

Locally instead of in Azure:

```bash
for tier in T0 T1 T2; do for cond in c1 c3; do
  for model in gpt-5.4 grok-4-20-reasoning llama-3.3-70b; do
    python phase2_coq/coq_pipeline.py --data data/fracas/fracas.xml \
      --dataset fracas --model "$model" --tier "$tier" --condition "$cond" \
      --stratified 3 --seed 0 \
      --output "phase2_coq/results/pilot__fracas__${model}__${tier}__${cond}.json"
done; done; done
```

### The gate — read `analysis/tables/coq_by_tier.csv`

| compilation rate | do this |
|---|---|
| **≥ 40%** | run WAVE 3 |
| **10–40%** | read `coq_error_taxonomy.csv`, fix the top category, re-pilot ($7.28 again) |
| **< 10%** | **STOP. Do not run WAVE 3.** Report the taxonomy instead (see below) |

**Why this gate is not paranoia.** I replayed 200 real Coq generations
through the fixed post-processor against coqc 8.12.2: **1/200 compiled,
raw and post-processed alike.** Post-processing repairs the lexer errors
(1,337 of 2,736 generations used `→ ∀ ∃ ∧` instead of ASCII) but that only
exposes the next layer — unbound identifiers (62), syntax errors (57),
type errors (34). The leverage has to come from the prompt, which is
exactly what T0/T1/T2 test. If it does not, the honest paper result is
"LLMs cannot produce compilable Coq for NLI, and here is the error
taxonomy" — which costs $7.28 to establish rather than $423.

---

## WAVE 2 — the two FOL conditions never run ($242.35)

All 43 existing FOL runs are **c1 (blind)** — verified three ways
(recorded `metadata.condition`, filename suffixes, code path). c2 and c3
are implemented but were never executed, so no Coq condition currently has
a FOL counterpart to compare against.

```bash
MODELS="gpt-4o gpt-5.4 deepseek-r1 deepseek-v4-pro grok-4-20 \
grok-4-20-reasoning llama-3.3-70b llama-4-maverick mistral-large-3"

for cond in c2 c3; do
  for ds in fracas fracas-translated fracas-extended fracas-multilabel oyxoy; do
    for model in $MODELS; do
      python phase2_fol/fol_pipeline.py --data "$ds" --model "$model" --condition "$cond"
    done
  done
done
```

| dataset | items | per condition |
|---|---|---|
| fracas | 342 | $14.44 |
| fracas-translated | 342 | $14.44 |
| fracas-extended | 427 | $18.03 |
| fracas-multilabel | 713 | $30.10 |
| oyxoy | 1,049 | $44.29 |
| **c2 + c3** | 51,714 gens | **$242.35** |

This wave is independent of WAVE 1 — run them in parallel. It is the
safer spend: the FOL pipeline demonstrably works (accuracy 0.513 over
23,670 items).

---

## WAVE 3 — Coq full grid ($415.72), only if WAVE 1 passed

3 tiers × 3 conditions × 9 models × 342 FraCaS items = 27,702 generations.

```bash
export AZURE_API_KEY=... AZURE_OPENAI_ENDPOINT=...
export ACR=youracr RG=nestor-rg STORAGE=yourstorage
bash deploy/azure_fanout.sh          # 81 containers

az storage file download-batch --account-name "$STORAGE" \
   -s nestor-results -d phase2_coq/results
```

Sequentially this is 3–5 days (API latency + 0.5 s sleep × 27,702). One
container per cell makes it ~30–60 min. Cells are independent and
resumable: `run_one_cell.sh` skips a cell whose output already exists, so
re-running only fills gaps.

| tier | c1 | c2 | c3 | total |
|---|---|---|---|---|
| T0 | $35.89 | $36.26 | $36.19 | $108.34 |
| T1 | $47.48 | $47.84 | $47.77 | $143.10 |
| T2 | $54.54 | $54.90 | $54.83 | $164.27 |
| | | | | **$415.72** |

**Rate limits, not compute, are the constraint.** 81 containers against
one Azure OpenAI deployment will throttle. Either raise the TPM quota or
fan out in waves by tier:

```bash
for t in T0 T1 T2; do TIERS=$t bash deploy/azure_fanout.sh; sleep 3600; done
```

**T3 ($309.65) is excluded by default** — its 12k-token prompts cost
almost as much as T0+T1+T2 combined. Add it only if T2 measurably beats
T1 in wave 3.

---

## WAVE 4 — analysis and paper (free)

```bash
python analysis/phase1_tables.py     # accuracy, sections, conditions
python analysis/judge_analysis.py    # judge scores, right-for-wrong-reasons
python analysis/fol_analysis.py      # FOL accuracy + error taxonomy
python analysis/agreement.py         # judge vs human kappa
python analysis/coq_analysis.py      # Coq compilation/proof/accuracy
python analysis/cross_pipeline.py    # per-item joins across pipelines
python analysis/audit.py             # coverage, defects, paper_numbers.csv
```

Run `audit.py` last and read `analysis/tables/audit_defects.csv` before
quoting any number. Every figure in the paper draws from
`analysis/tables/paper_numbers.csv` (98 values), so nothing is hardcoded.

---

## The three conditions, and what each measures

| cond | model is given | measures |
|---|---|---|
| **c1** | nothing | formalise *and* decide — confounds two abilities |
| **c2** | its own Phase 1 answer | does its own prior answer help or anchor it |
| **c3** | the gold relation | formalisation ability alone — can it *prove* a known fact |

c3 maps gold `yes/no/unknown` → `Entailment/Contradiction/Unknown` (the
FOL c3 vocabulary) and additionally states which theorem must close;
`yes` alone is meaningless in a Coq prompt.

**A C1 run cannot be contaminated silently.** The C1–C4 menu lives in the
prompt template and is removed by a regex; if a template edit breaks the
`=== CONDITION ===` markers, `build_coq_prompt` raises rather than leaking
the gold label into a "blind" run. If you see `C1 prompt contamination`,
fix the template — never suppress it.

---

## Gotchas that will cost you a whole run

- **`COQC_PATH` unset** → every item fails identically. The container sets
  it; if running locally, export it.
- **`OCAMLLIB` unset** with a conda Coq → `Fatal error: exception
  Not_found` on every call including `--version`.
- **No volume at `/results`** → a finished container takes its results
  with it.
- **API keys in `--environment-variables`** are readable via `az container
  show`. `azure_fanout.sh` uses `--secure-environment-variables`.
- **`coqc_version` is recorded** in every result file's metadata. The
  compiler version changes what compiles; results from different images
  stay distinguishable.
