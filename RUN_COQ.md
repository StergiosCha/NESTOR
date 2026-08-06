# Running Phase 2b (Coq) — runbook

Everything here was verified offline against **coqc 8.12.2**. Numbers in
the cost table are computed from measured token counts, not estimated:
prompt sizes from the real prompt builder over 25 FraCaS items, output
size from 2,736 real generations (mean 795 tokens), and the retry factor
from the 23,670 completed FOL items (mean attempts **1.252**).

---

## 0. What was wrong before, and what changed

Four defects made the previous Phase 2b numbers uninterpretable. All are
fixed in `phase2_coq/coq_pipeline.py`; each fix was checked against a real
compiler.

| # | Defect | Consequence | Status |
|---|---|---|---|
| 1 | `get_section_from_id` took `id.split("-")[1]`, which on the loader's real ids (`fracas-1` … `fracas-346`) returns the **problem number**, not the section | `SECTION_FILES` never matched, so **T2 and T3 silently loaded only `Montague.v`**. The section-matched-foundation condition had never actually run. | fixed: section computed from FraCaS problem-number boundaries |
| 2 | `--section 1` filtered with `startswith`, matching `fracas-1` and `fracas-100`–`199` | **111 items spanning every section**. The pilot command in the brief would have run the wrong items. | fixed: `select_items_by_section`, verified 80/33/28/55/23/31/71/8/13 = 342 |
| 3 | `proof_complete = compiled and "Abort" not in coq_code` | Wrong in both directions. A correct entailment answer *is* `entailment…Qed` + `contradiction…Abort`, and this scored it **incomplete**; a file with no theorems at all scored **complete**. | fixed: requires an actual `Qed.` |
| 4 | C2/C4 read `fracas_results_azure.json` — **gpt-4o only, 30 of 342 items** | 91% of items silently got `"unknown"` as the "previous prediction", and every model was shown gpt-4o's answers. | fixed: reads the real per-model Phase 1 files; coverage now 342/342 for every model |

### The `Hypothesis` → `Axiom` fix does not work

The brief prescribes `re.sub(r'^Hypothesis\b','Axiom', code)`. **Verified
against coqc: this changes nothing.** Both keywords declare a *proof term*
of the stated proposition, so a following
`Theorem entailment : premise -> hypothesis.` is ill-typed either way:

```
Error: The term "premise" has type "exists x : Entity, ..."
       which should be Set, Prop or Type.
```

| probe | raw | after `Hypothesis`→`Axiom` | after `Definition … : Prop :=` |
|---|---|---|---|
| `Hypothesis premise : exists …` + `Theorem … : premise -> hypothesis` | exit 1 | **exit 1 (unchanged)** | **exit 0** |

`Definition NAME : Prop := …` names the proposition itself, so it can
appear on either side of `->`. That is what the prompts now mandate.

### The real dominant failure was the lexer

Of 2,736 pilot generations, **1,337 contain Unicode logic symbols**
(`→ ∀ ∃ ∧ ⇒`) instead of ASCII (`-> forall exists /\`). coqc rejects these
outright (`Syntax Error: Lexer: Undefined token`), losing the whole file
before any semantics is checked. `normalise_unicode` now runs first in
post-processing. Expect your models to do this too.

**Honest caveat.** On 200 real generations, raw compiled 1/200 and
post-processed also 1/200. Repairing the lexer errors exposes the next
layer — unbound identifiers (62), syntax errors (57), type errors (34).
Post-processing alone does **not** rescue these generations; the leverage
is in the prompt, which is what T0/T1/T2 test. **Hence the pilot gate in
§3 — do not skip it.**

---

## 1. Install Coq

Not needed on the machine that calls the API — but `coqc` must exist
wherever you run the pipeline, or every item fails identically.

```bash
# macOS (arm64): opam builds cleanly but slowly; conda osx-64 under
# Rosetta is faster and was what these fixes were verified against.
micromamba create -y -p ./coq812 --platform osx-64 -c conda-forge coq

# coqc needs OCAMLLIB set or it dies with "Fatal error: exception Not_found"
export OCAMLLIB=$PWD/coq812/lib/ocaml
export COQC_PATH=$PWD/coq812/bin/coqc
$COQC_PATH --version      # The Coq Proof Assistant, version 8.12.2
```

Linux is simpler: `conda install -c conda-forge coq` (or the distro
package). Confirm before running anything:

```bash
printf 'Theorem t : True.\nProof. exact I. Qed.\n' > /tmp/t.v && $COQC_PATH /tmp/t.v && echo OK
```

## 2. Environment

```bash
cp .env.example .env      # then fill in:
#   AZURE_API_KEY, AZURE_OPENAI_ENDPOINT, AZURE_AI_ENDPOINT
#   LITELLM_HOST, LITELLM_ILSP_EVAL_API_KEY
#   GPT_5_4_PRO_ENDPOINT, GPT_5_4_PRO_API_KEY
export COQC_PATH=/abs/path/to/coqc      # REQUIRED
export COQ_TIMEOUT=60                   # per-item compile budget
```

---

## 3. Pilot gate — run this first ($7.28)

486 generations: 3 tiers × 2 conditions × 3 models × 27 items. **$7.28.** The
stratified sample takes 3 items per FraCaS section, so all nine
phenomena are covered — a plain `--limit 27` would give you 27 items of
section 1 only and tell you nothing.

```bash
cd /path/to/NESTOR
for tier in T0 T1 T2; do
  for cond in c1 c3; do
    for model in gpt-5.4 grok-4-20-reasoning llama-3.3-70b; do
      python phase2_coq/coq_pipeline.py \
        --data data/fracas/fracas.xml \
        --dataset fracas \
        --model "$model" \
        --tier "$tier" \
        --condition "$cond" \
        --stratified 3 --seed 0 \
        --output "phase2_coq/results/pilot__fracas__${model}__${tier}__${cond}.json"
    done
  done
done

python analysis/coq_analysis.py     # tables + figures over whatever exists
```

**Gate — decide from the pilot's measured compilation rate:**

| Pilot compilation rate | Read | Do |
|---|---|---|
| **≥ 40%** | prompts work | run the full grid (§4), $415.72 |
| **10–40%** | partly working | check `coq_error_taxonomy.csv`, fix the top category, re-pilot |
| **< 10%** | prompt changes did not land | **stop.** Do not spend $415.72. The finding is "LLMs cannot produce compilable Coq for NLI"; report the error taxonomy instead (§6) |

Sanity checks on the pilot output, before believing any of it:

```bash
# T2 must actually receive section-matched files (defect 1)
python - <<'EOF'
import sys; sys.path.insert(0,'phase2_coq'); sys.path.insert(0,'.')
import importlib.util
spec=importlib.util.spec_from_file_location("cp","phase2_coq/coq_pipeline.py")
cp=importlib.util.module_from_spec(spec); spec.loader.exec_module(cp)
for i in (1,100,200,300,340):
    s=cp.get_section_from_id(f"fracas-{i}")
    print(f"fracas-{i}: section {s} -> {cp.SECTION_FILES[s]}")
EOF
```

---

## 4. Full run (only if the pilot passes)

3 tiers × 3 conditions × 9 models × 342 items = **27,702 generations,
$415.72**.

```bash
MODELS="gpt-4o gpt-5.4 deepseek-r1 deepseek-v4-pro grok-4-20 \
grok-4-20-reasoning llama-3.3-70b llama-4-maverick mistral-large-3"

for tier in T0 T1 T2; do
  for cond in c1 c2 c3; do
    for model in $MODELS; do
      out="phase2_coq/results/fracas__${model}__${tier}__${cond}.json"
      [ -f "$out" ] && { echo "skip $out"; continue; }   # resumable
      python phase2_coq/coq_pipeline.py \
        --data data/fracas/fracas.xml --dataset fracas \
        --model "$model" --tier "$tier" --condition "$cond" \
        --output "$out"
    done
  done
done
```

### Cost and time

Measured prompt sizes (tokens, mean over 25 FraCaS items):

| tier | c1 | c2 | c3 | note |
|---|---|---|---|---|
| T0 | 1,886 | 1,941 | 1,930 | syntax only |
| T1 | 3,630 | 3,685 | 3,674 | + Montague.v |
| T2 | 4,693 | 4,748 | 4,737 | + section-matched files |
| T3 | 11,990 | 12,045 | 12,034 | **excluded** — $309.65 alone |

Cost per tier (9 models × 342 items × 3 conditions, avg list price
$1.72/1M in, $7.63/1M out, ×1.252 retries):

| tier | c1 | c2 | c3 | tier total |
|---|---|---|---|---|
| T0 | $35.89 | $36.26 | $36.19 | **$108.34** |
| T1 | $47.48 | $47.84 | $47.77 | **$143.10** |
| T2 | $54.54 | $54.90 | $54.83 | **$164.27** |
| | | | | **$415.71** |

Wall-clock: the pipeline sleeps 0.5 s between items and is sequential, so
one tier×condition×model over 342 items is roughly 30–60 min depending on
the model. The full grid is ~27,702 × (latency + 0.5 s) — **budget 3–5
days sequentially**, or parallelise across models (each writes its own
file, so they are independent).

**T3 is excluded.** Its 12k-token prompts cost $309.65 for the same 342
items — nearly as much as T0+T1+T2 combined. Add it only if T2 shows foundation files help.

---

## 5. Optional: the two FOL conditions you have not run

All 43 existing FOL runs are **c1** — verified three ways (recorded
`metadata.condition`, filename suffixes, and the code path). C2 and C3
are implemented but were never executed, so no Coq condition currently
has a FOL counterpart.

**The FOL grid is also incomplete: 43 of 45 cells.** `deepseek-r1` is
missing on `fracas-extended` and `oyxoy`. Backfilling those two cells is
1,476 items, **$6.92** — do this regardless of what else you run, because
otherwise every per-model FOL comparison silently drops a model on two
datasets.

```bash
for ds in fracas-extended oyxoy; do
  python phase2_fol/fol_pipeline.py --data "$ds" --model deepseek-r1 --condition c1
done
```

| dataset | items | cost per condition |
|---|---|---|
| fracas | 342 | $14.44 |
| fracas-translated | 342 | $14.44 |
| fracas-extended | 427 | $18.03 |
| fracas-multilabel | 713 | $30.10 |
| oyxoy | 1,049 | $44.29 |
| **all five, one condition** | | **$121.29** |
| **c2 + c3** | 51,714 generations | **$242.59** |

```bash
for cond in c2 c3; do
  for ds in fracas fracas-translated fracas-extended fracas-multilabel oyxoy; do
    for model in $MODELS; do
      python phase2_fol/fol_pipeline.py --data "$ds" --model "$model" --condition "$cond"
    done
  done
done
```

This is the better-value spend: it completes a 3-condition × 5-dataset
grid on a pipeline that already works (FOL accuracy 0.513 over 23,670
items), and it makes the Coq conditions interpretable by comparison.

---

## 6. Analysis

```bash
python analysis/phase1_tables.py     # Phase 1 accuracy, sections, conditions
python analysis/judge_analysis.py    # judge scores, right-for-wrong-reasons
python analysis/fol_analysis.py      # FOL accuracy + error taxonomy
python analysis/agreement.py         # judge vs human kappa
python analysis/coq_analysis.py      # Coq compilation/proof/accuracy per tier
python analysis/cross_pipeline.py    # per-item joins across all pipelines
```

`coq_analysis.py` degrades gracefully: with no Coq results it writes
correctly-shaped empty tables and placeholder figures, so the analysis
and paper build run before Phase 2b exists.

---

## 7. Gotchas

- **`COQC_PATH` unset** → every item fails identically with
  `ERROR: coqc not found`. The taxonomy will read `coqc_missing`; that is
  a configuration failure, not a result.
- **`OCAMLLIB` unset** (conda Coq) → `Fatal error: exception Not_found`
  on every invocation, including `--version`.
- **C1 contamination guard.** The C1–C4 menu lives in the template and is
  removed by a regex. If an edit breaks the `=== CONDITION ===` /
  `=== END CONDITION ===` markers, `build_coq_prompt` now raises rather
  than silently leaking the gold label into a "blind" run. If you see
  `C1 prompt contamination`, fix the template — do not suppress it.
- **C3 gold vocabulary.** Gold is stored `yes/no/unknown` but is mapped
  to `Entailment/Contradiction/Unknown` to match the FOL C3 wording, and
  C3 additionally states *which* theorem must close. Raw `yes` in a Coq
  prompt is meaningless.
- **`Admitted.`** compiles and would score as a completed proof. Post-
  processing rewrites it to `Abort.`.
- **Resumability.** The loops above skip existing output files. Deleting
  a file re-runs that cell.

---

## 8. Running the whole grid in Azure containers (recommended)

`coqc` must exist on the machine that runs the pipeline, and the grid is
embarrassingly parallel — one container per (model × tier × condition)
cell, each writing its own file. `deploy/` has the three pieces.

Sequentially the full grid is ~27,702 items × (API latency + 0.5 s
sleep) — **3–5 days**. Fanned out over 81 containers it is roughly the
duration of one cell, **30–60 minutes**.

```bash
# 1. build (linux/amd64 so coqc comes from Debian; the build FAILS if
#    coqc cannot compile a smoke file, which is the point)
az acr build -r "$ACR" -t nestor:latest -f deploy/Dockerfile .

# 2. fan out: 81 containers for T0-T2 x c1/c3/c2 x 9 models
export ACR=youracr STORAGE=yourstorage RG=nestor-rg
export AZURE_API_KEY=... AZURE_OPENAI_ENDPOINT=...
bash deploy/azure_fanout.sh

# 3. collect from the file share
az storage file download-batch \
   --account-name "$STORAGE" -s nestor-results -d phase2_coq/results
```

Pilot first, by narrowing the same script:

```bash
MODELS="gpt-5.4 grok-4-20-reasoning llama-3.3-70b" \
TIERS="T0 T1 T2" CONDS="c1 c3" \
EXTRA="--stratified 3 --seed 0" \
bash deploy/azure_fanout.sh          # 18 containers, $7.28
```

Notes that matter:

- **API keys go in `--secure-environment-variables`**, never in
  `--environment-variables` (those are readable via `az container show`).
  `azure_fanout.sh` already does this.
- **Mount a volume at `/results`.** Without it, a container that exits
  takes its results with it.
- **Cells are resumable.** `run_one_cell.sh` skips a cell whose output
  file already exists, so re-running the fan-out only fills gaps.
- **Rate limits are the real constraint**, not compute. 81 containers
  hitting one Azure OpenAI deployment will throttle; either raise the
  TPM quota or fan out in waves by tier (`TIERS=T0 bash …`).
- `coqc_version` is recorded in every result file's metadata, so results
  produced by different images stay distinguishable.
