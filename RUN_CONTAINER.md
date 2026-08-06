# Running NESTOR Phase 2 in Azure containers

Close your laptop. One container per (model × tier × condition) cell; each
writes its own file to a shared volume, so cells are independent and the
whole grid finishes in about the time of one cell.

Everything below was validated locally except the `az` calls themselves —
there is no Azure CLI and no subscription access in the authoring
environment, so **the first `az acr build` is the first real test.**

---

## 0. One-time setup (~10 min)

```bash
cd /path/to/NESTOR
export RG=nestor-rg LOC=westeurope
export ACR=nestoracr$RANDOM          # must be globally unique
export STORAGE=nestorst$RANDOM       # must be globally unique, lowercase
export SHARE=nestor-results

az login
az group create -n "$RG" -l "$LOC"

# Registry (admin user is required: ACI pulls with username/password)
az acr create -n "$ACR" -g "$RG" --sku Basic
az acr update -n "$ACR" --admin-enabled true

# Shared volume for results
az storage account create -n "$STORAGE" -g "$RG" -l "$LOC" --sku Standard_LRS
KEY=$(az storage account keys list -g "$RG" -n "$STORAGE" --query "[0].value" -o tsv)
az storage share create -n "$SHARE" --account-name "$STORAGE" --account-key "$KEY"

# Build the image IN Azure (no local docker needed)
az acr build -r "$ACR" -t nestor:latest -f deploy/Dockerfile .
```

The build compiles a smoke `.v` file. If `coqc` is broken the build
**fails there** rather than turning every one of 27,702 items into an
identical `coqc_missing` error.

Save these exports — you need them again to download results.

---

## 1. Launch

```bash
set -a; . ./.env; set +a          # loads AZURE_API_KEY and the endpoints

MODELS="gpt-5.4 grok-4-20-reasoning llama-3.3-70b" \
TIERS="T0 T1 T2" CONDS="c1 c3" \
EXTRA="--stratified 3 --seed 0" PREFIX="pilot__" \
bash deploy/azure_fanout.sh
```

18 containers, **$16.88** ($15.81 API + $1.07 compute), ~30–60 min wall clock. It asks before launching;
`YES=1` skips the prompt.

Full grid instead (81 containers, **$695.21**):

```bash
MODELS="gpt-4o gpt-5.4 deepseek-r1 deepseek-v4-pro grok-4-20 \
grok-4-20-reasoning llama-3.3-70b llama-4-maverick mistral-large-3" \
TIERS="T0 T1 T2" CONDS="c1 c2 c3" bash deploy/azure_fanout.sh
```

The fan-out refuses to start if: `az` is missing, you are not logged in,
`AZURE_API_KEY` is unset, the image is not in the registry, or the storage
key cannot be read. Each of those would otherwise surface 81 containers
later.

---

## 2. Monitor (or just come back tomorrow)

```bash
bash deploy/azure_status.sh          # snapshot: state + restart count
bash deploy/azure_status.sh -w       # refresh every 60s
bash deploy/azure_status.sh -l nestor-gpt-5-4-t0-c1   # tail one log
```

`Succeeded` = cell complete. `Failed` = look at the log; the cell retries
3× internally with 60/120s backoff before giving up.

---

## 3. Download and analyse

```bash
KEY=$(az storage account keys list -g "$RG" -n "$STORAGE" --query "[0].value" -o tsv)
az storage file download-batch --account-name "$STORAGE" --account-key "$KEY" \
  -s "$SHARE" -d phase2_coq/results

python analysis/coq_analysis.py
python analysis/audit.py
./watch_pilot.sh 0                  # quick per-cell summary
```

Read `analysis/tables/coq_by_tier.csv` for the tier comparison and
`analysis/tables/coq_error_taxonomy.csv` for what is still failing.

---

## 4. Clean up

```bash
bash deploy/azure_cleanup.sh         # terminated containers only
```

Deletes only containers in a terminal state, and asks first. A `Running`
container still holds items it has not written; deleting it loses them.
`ALL=1` overrides but requires typing `delete-running`.

Storage is a few cents a month; delete the whole group when done:
`az group delete -n "$RG" --yes`.

---

## Why each guard exists

| guard | without it |
|---|---|
| `.dockerignore` excludes `.env` | your live API key is baked into an image layer, readable by anyone who can pull it, and stays in the registry after deletion |
| smoke `.v` compiled at build time | a broken `coqc` fails silently at run time on every item |
| keys via `--secure-environment-variables` | `az container show` prints them in plain text |
| preflight in `run_one_cell.sh` | a missing key burns a container to produce 27 identical failures |
| per-item writes + in-cell resume | an interrupt at item 26 of 27 discards 26 items and their API spend |
| 3× retry with backoff | one transient Azure fault kills a cell that was 90% done |
| logs written to the volume | container logs vanish with the instance; a failed run becomes undiagnosable |
| `LLM_TIMEOUT=300` | reasoning models exceed the 60s default and die mid-cell (this actually happened) |
| skip cells whose file exists | re-running the fan-out double-charges for completed work |
| `coqc` version in image + metadata | cells compiled by different versions are not comparable, and nobody can tell afterwards |

## Known gaps

- The `az` commands are unvalidated — no Azure access here. Expect to fix
  a name collision or a quota message on first run.
- ACI has a per-region container quota (often 100); 81 containers plus
  anything else may hit it. Throttle by tier if so:
  `for t in T0 T1 T2; do TIERS=$t bash deploy/azure_fanout.sh; sleep 3600; done`
- Costs are recomputed from the first real cell: measured retry factor
  1.593 (not the FOL-derived 1.252) and reasoning traces billed at ~3x the
  795-token baseline. See `analysis/tables/cost_estimates.json` for the
  sensitivity range ($529–847 for the full grid).
