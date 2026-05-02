# Contributing to NESTOR

This guide gets a new contributor from a fresh clone to a working test of every phase.

*Work in progress*

## 1. Prerequisites

### Python

Python 3.10+ 

### Coq

Coq 8.18+ with `coqc` binary on your PATH (or set `COQC_PATH` in `.env`).

Refer to [Rocq official website](https://rocq-prover.org/install#windows).

- **Verify installation**: `coqc --version`
- **Find binary path**: `where coqc`

### Prover9 + MACE4

Required for the FOL pipeline. Binaries must be on your PATH (or set `PROVER9_PATH` / `MACE4_PATH` in `.env`).

Refer to [Prover9 and Mace4](https://www.cs.unm.edu/~mccune/prover9/) and [Prover9](https://prover9.org/).

- **Verify**: `prover9 -h`
- **Find binary path**: `where coqc` / `where mace4`

### Azure AI Foundry account

All LLM calls go through Azure AI Foundry. You need:

- An Azure AI Foundry resource with at least one model deployed.
- The `AZURE_API_KEY` for that resource — one key covers both endpoints.
- The endpoint URLs 

See `utils/models.py` for the full model registry.

## 2. Clone and configure

```bash
git clone https://github.com/StergiosCha/NESTOR.git nestor
cd nestor
cp .env.example .env
```

Open `.env` and fill in `AZURE_API_KEY`. 
`.env` is gitignored; never commit your secrets.

## 3. Environment variables

Full reference to `.env` configuration:

| Variable | Required | Description |
|---|---|---|
| `AZURE_API_KEY` | Everywhere | Authenticates against both Azure endpoints |
| `AZURE_OPENAI_ENDPOINT` | Everywhere | Azure OpenAI Service endpoint (GPT models) |
| `AZURE_OPENAI_API_VERSION` | Everywhere | API version string (e.g. `2024-12-01-preview`) |
| `AZURE_AI_ENDPOINT` | Everywhere | Azure AI Inference endpoint (Llama, DeepSeek, Mistral) |
| `COQC_PATH` | Phase 2 Coq | Path to `coqc`; defaults to `coqc` (PATH lookup) |
| `PROVER9_PATH` | Phase 2 FOL | Path to `prover9`; defaults to `prover9` (PATH lookup) |
| `MACE4_PATH` | Phase 2 FOL | Path to `mace4`; defaults to `mace4` (PATH lookup) |
| `MAX_RETRIES` | Phase 2 FOL & Coq | Verification loop retries (default: 3) |
| `PROVER_TIMEOUT` | Phase 2 FOL | Prover9/MACE4 timeout in seconds (default: 30) |
| `COQ_TIMEOUT` | Phase 2 Coq | `coqc` timeout in seconds (default: 60) |
| `LLM_RATE_LIMIT` | Phase 1 | Seconds between LLM calls (default: 0.3) |
| `FRACAS_XML_URL` | Phase 1 | URL to download FraCaS XML (auto-download on first run) |

If a required variable is missing, the pipeline will fail or revert to default configuration.

## 4. Create virtual env for Python and install dependencies

Pick the workflow that suits you best.

### pip + venv

```bash
python3 -m venv .venv
source .venv/bin/activate       # Windows: .venv\Scripts\activate
pip install -r requirements.txt
```

### uv

```bash
uv venv
source .venv/bin/activate       # Windows: .venv\Scripts\activate
uv pip install -r requirements.txt
```
*Once we have `pyproject.toml` and `uv.lock`, this becomes `uv sync`.*

### conda

```bash
conda create -n nestor
conda activate nestor
pip install -r requirements.txt
```

## 5. Running each phase pipeline

See [README](./README.md).


## 6. Adding a new Azure model

1. Deploy the model in Azure AI Foundry under the same resource.
2. Add an entry to `utils/models.py`:
   ```python
   "my-model": {
       "deployment": "my-model-deployment", # exact deployment name in Azure
       "provider": "azure-openai",          # GPT-family (Azure OpenAI Service)
       # or
       "provider": "azure-ai",              # Llama, DeepSeek, Mistral, etc. (Azure AI Inference)
   },
   ```
3. Run any pipeline with the `--model my-model` argument. 


## 7. Where results land

|Phase | Path | Tracked |
|---|---|---|
| Phase 1: LLM-only NLI | `phase1_nli_eval/fracas_results*.json`, `fracas_summary*.txt` | gitignored |
| Phase 2: FOL pipeline | `phase2_fol/results/*.json` | gitignored |
| Phase 2: Coq pipeline | `phase2_coq/results/*.json` | gitignored |

Results are intentionally gitignored to prevent each contributor's local results from being accidentally overwritten.


## 8. Branching strategy

## 9. Troubleshooting
