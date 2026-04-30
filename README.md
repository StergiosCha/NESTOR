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
  ├── English FraCaS (346 items, 9 phenomena)
  ├── Greek FraCaS
  └── OYXOY-NLI (1,762 pairs, multi-label)

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
├── data/
│   ├── fracas/            # English FraCaS (fracas.xml)
│   ├── greek_fracas/      # Greek FraCaS (to be added)
│   └── oyxoy/             # OYXOY-NLI (to be added)
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

```bash
cd phase1_nli_eval
python fracas_eval_azure.py --model gpt-4o --limit 10
```

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

Set your Azure API key:
```bash
export AZURE_KEY="your-key-here"
```

Both pipelines read from environment variables:
- `AZURE_KEY` — API key
- `AZURE_OPENAI_ENDPOINT` — GPT models endpoint
- `AZURE_AI_ENDPOINT` — Llama/DeepSeek endpoint
- `COQC_PATH` — path to coqc (default: `coqc`)
- `PROVER9_PATH` / `MACE4_PATH` — paths to provers (default: `prover9` / `mace4`)

## Authors

Stergios Chatzikyriakidis — University of Crete
