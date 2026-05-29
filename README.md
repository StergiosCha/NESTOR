# NESTOR

**Neural-Symbolic Testing & Ontological Reasoning**

A framework for evaluating LLMs on Natural Language Inference (NLI) using formal verification with FOL (Prover9/MACE4) and Coq.

## Overview

NESTOR tests whether LLMs can perform reliable natural language inference, and then verifies those inferences using two formal methods in parallel:

1. **First-Order Logic** — translate NL to FOL, verify with Prover9 (entailment) and MACE4 (countermodel search)
2. **Coq proof assistant** — formalise in dependent type theory, compile proof with coqc

A verification loop (k=3) feeds prover/compiler errors back to the LLM for self-correction.

## Architecture

```
Phase 1: LLM-only NLI evaluation
  ├── English FraCaS         (346 items, 9 phenomena, single-label)
  ├── Translated FraCaS      (Greek translation of FraCaS, single-label)
  ├── Extended FraCaS        (Greek FraCaS extension, ids 347+, single-label)
  ├── Multilabel FraCaS      (Greek, multi-label)
  └── OYXOY-NLI              (Greek, multi-label, common-sense oriented)

Phase 2: Formal verification (parallel paths)
  ├── FOL path: NL → FOL → Prover9/MACE4
  └── Coq path: NL → Coq → coqc
      ├── Direct approach (formalise P, H)
      └── Valentino approach (formalise explanation E)

Phase 3: Analysis
  ├── 2×2 matrix: FOL success/fail × Coq success/fail
  ├── Three-way comparison: LLM-only vs FOL+Prover vs Coq
  └── Verification loop effectiveness
```

## Repository Structure

```
NESTOR/
├── clients/               # Shared LLM client setup
│   └── azure.py           # get_azure_client, get_ai_client, call_llm
│
├── utils/                 # Shared utilities
│   ├── models.py          # model registry
│   └── fracas.py          # legacy FraCaS loader
│
├── phase1_nli_eval/       # Phase 1: LLM-only NLI
│   ├── fracas_eval.py     # OpenAI evaluation script
│   ├── fracas_eval_azure.py  # Azure evaluation script
│   ├── prompts/           # Prompt templates
│   │   ├── en_fracas.txt
│   │   ├── gr_fracas_single.txt
│   │   └── gr_oyxoy_multi.txt
│   └── results/           # Stored results
│
├── phase2_fol/            # Phase 2: FOL + Prover9/MACE4
│   ├── fol_pipeline.py    # Full pipeline with verification loop
│   └── prompts/
│       ├── nl_to_fol.txt
│       └── fol_fix.txt
│
├── phase2_coq/            # Phase 2: Coq verification
│   ├── coq_pipeline.py    # Full pipeline (Direct + Valentino)
│   ├── prompts/
│   │   ├── nl_to_coq.txt
│   │   ├── coq_fix.txt
│   │   └── valentino_coq.txt
│   └── lib/               # Core Coq libraries for reference
│
├── phase3_loop/           # Phase 3: Comparison & analysis
│   └── compare.py
│
├── coq_foundations/        # Coq formalisation library (37 files)
│   ├── MTT_base.v, MTTbase.v
│   ├── Quantifiers.v, FCS.v
│   ├── Montague.v, MontagueFragment.v
│   ├── BarwiseCooper.v
│   ├── Coqification_1-5.v
│   └── ...
│
├── data/                  # Datasets + unified loaders
│   ├── schema.py          # Sample dataclass, LABELS, SOURCES, FRACAS_LABEL_MAP, OYXOY_TO_FRACAS_SECTION
│   ├── loaders.py         # load_fracas, load_translated_fracas, load_extended_fracas,
│   │                      # load_multilabel_fracas, load_oyxoy → list[Sample]
│   ├── fracas/            # English FraCaS (fracas.xml)
│   ├── translated_fracas/ # Greek translation of FraCaS (translated_fracas.xml)
│   ├── extended_fracas/   # Greek FraCaS extension, ids 347+ (extended_fracas.xml)
│   ├── multilabel_fracas/ # Greek multilabel FraCaS (multilabel_fracas.json)
│   └── oyxoy/             # OYXOY-NLI (OYXOY.json)
│
├── docs/
│   ├── protocol.tex       # Full experimental protocol
│   ├── project_athens.tex # Project presentation
│   └── experiment_design.tex
│
└── infrastructure/
    └── azure_guide_crete.tex
```

## Requirements

```bash
pip install openai
```

For FOL verification:
- [Prover9 & MACE4](https://www.cs.unm.edu/~mccune/prover9/) in PATH

For Coq verification:
- Coq 8.18+ (`coqc` in PATH)

## Usage

### Phase 1: LLM-only NLI

Run single combination from project root via `nli_pipeline`:

```bash
python -m phase1_nli_eval.nli_pipeline \
    --data fracas --model gpt-4o --technique zero-shot --language en \
    [--resume] [--limit N]
```

- `--data`: `fracas | fracas-translated | fracas-extended | fracas-multilabel | oyxoy`
- `--model`: any key from `clients/models.py::MODELS`
- `--technique`: `zero-shot | few-shot | cot`
- `--language`: prompt-body language, `en | el`
- `--resume`: skip samples already present in the per-combo result JSON
- `--limit N`: process at most N pending samples

One result JSON per combination is written to `phase1_nli_eval/results/{dataset}__{model}__{technique}__{language}.json`. Each file carries a `summary` block (`total`, `parse_fail`, `llm_error`, `success_count`, `accuracy`) recomputed from the full results list on every flush.

Bulk sweep via `run_bulk`:

```bash
python -m phase1_nli_eval.run_bulk --config phase1_nli_eval/sweep_config.yaml
```

The YAML lists the four dimensions explicitly; the runner expands the Cartesian product, executes each combo sequentially (delegating to `nli_pipeline.run`), isolates per-combo failures, and prints a final PASS/FAIL table sourced from each JSON's `summary`. Exit code is non-zero if any combo fails. See `sweep_config.yaml` for the schema.

### Phase 2: FOL verification

```bash
cd phase2_fol
python fol_pipeline.py --data ../data/fracas/fracas.xml --model gpt-4o --limit 10
```

### Phase 2: Coq verification

```bash
cd phase2_coq
# Direct approach
python coq_pipeline.py --data ../data/fracas/fracas.xml --model gpt-4o --approach direct
# Valentino approach (requires explanations)
python coq_pipeline.py --data ../data/fracas/fracas.xml --model gpt-4o --approach valentino
```

### Phase 3: Comparison

```bash
cd phase3_loop
python compare.py --fol ../phase2_fol/results/fol_gpt4o.json \
                  --coq ../phase2_coq/results/coq_gpt4o.json \
                  --phase1 ../phase1_nli_eval/results/fracas_results_azure.json
```

## Approaches

### Direct (for FraCaS)
Formalise premise P and hypothesis H directly. The proof itself serves as the explanation. Best for linguistically clean datasets where P alone contains enough information.

### Valentino (for OYXOY / common-sense)
Based on [Valentino et al. (ACL 2025)](https://arxiv.org/abs/2502.12345). Formalise the LLM's explanation E as axioms, then prove P ∪ E ⊨ H. Useful when common-sense knowledge bridges the gap between P and H.

## Configuration
Copy `.env.example` to `.env` and fill in `AZURE_API_KEY`

`.env.example` lists every variable the pipelines read (Azure endpoints, tool paths, timeouts, max retries). See [CONTRIBUTING.md](CONTRIBUTING.md) for setup and installation instructions.

## Authors

Stergios Chatzikyriakidis — University of Crete
