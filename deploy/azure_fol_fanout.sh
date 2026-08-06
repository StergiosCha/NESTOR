#!/usr/bin/env bash
# Fan the FOL grid out over Azure Container Instances, one container per
# (dataset x model x condition) cell. Same image as the Coq fan-out.
#
# Three jobs this covers:
#   REPAIR    the truncated fracas-multilabel/deepseek-r1/c1 run (2 of 713)
#   BACKFILL  deepseek-r1 on fracas-extended and oyxoy (never run)
#   c2 / c3   conditions implemented but never executed for FOL
set -uo pipefail
RG="${RG:-nestor-rg}"
LOC="${LOC:-westeurope}"
ACR="${ACR:?set ACR}"
IMAGE="$ACR.azurecr.io/nestor:latest"
STORAGE="${STORAGE:?set STORAGE}"
SHARE="${SHARE:-nestor-results}"
CPU="${CPU:-1}"; MEM="${MEM:-2}"
EXTRA="${EXTRA:-}"

MODELS="${MODELS:-gpt-4o gpt-5.4 deepseek-r1 deepseek-v4-pro grok-4-20 \
grok-4-20-reasoning llama-3.3-70b llama-4-maverick mistral-large-3}"
DATASETS="${DATASETS:-fracas}"
CONDS="${CONDS:-c3}"

command -v az >/dev/null || { echo "FATAL: az CLI not installed"; exit 1; }
az account show >/dev/null 2>&1 || { echo "FATAL: run 'az login'"; exit 1; }
: "${AZURE_API_KEY:?FATAL: AZURE_API_KEY not exported (source .env)}"
az acr repository show -n "$ACR" --image nestor:latest >/dev/null 2>&1 \
  || { echo "FATAL: $IMAGE not in registry; run az acr build first"; exit 1; }

KEY=$(az storage account keys list -g "$RG" -n "$STORAGE" --query "[0].value" -o tsv) \
  || { echo "FATAL: cannot read storage key"; exit 1; }
ACR_USER=$(az acr credential show -n "$ACR" --query username -o tsv 2>/dev/null) || true
ACR_PASS=$(az acr credential show -n "$ACR" --query "passwords[0].value" -o tsv 2>/dev/null) || true
[ -n "${ACR_USER:-}" ] || { echo "FATAL: az acr update -n $ACR --admin-enabled true"; exit 1; }

total=0
for ds in $DATASETS; do for c in $CONDS; do for m in $MODELS; do
  total=$((total+1)); done; done; done
echo "About to launch $total FOL containers."
echo "  datasets:   $DATASETS"
echo "  conditions: $CONDS"
echo "  models:     $MODELS"
if [ "${YES:-0}" != "1" ]; then
  printf "Proceed? [y/N] "; read -r a
  case "$a" in y|Y) ;; *) echo aborted; exit 0;; esac
fi

n=0; up=0; bad=0
for ds in $DATASETS; do for c in $CONDS; do for m in $MODELS; do
  name="nestor-fol-$(echo "${ds}-${m}-${c}" | tr '[:upper:]' '[:lower:]' \
        | tr -c 'a-z0-9-' '-' | sed 's/--*/-/g; s/^-//; s/-$//')"
  n=$((n+1))
  if az container show -g "$RG" -n "$name" >/dev/null 2>&1; then
    echo "[$n/$total] exists, skipping: $name"; continue
  fi
  if az container create \
      --resource-group "$RG" --location "$LOC" --name "$name" \
      --image "$IMAGE" --cpu "$CPU" --memory "$MEM" \
      --os-type Linux --restart-policy Never \
      --registry-login-server "$ACR.azurecr.io" \
      --registry-username "$ACR_USER" --registry-password "$ACR_PASS" \
      --azure-file-volume-account-name "$STORAGE" \
      --azure-file-volume-account-key "$KEY" \
      --azure-file-volume-share-name "$SHARE" \
      --azure-file-volume-mount-path /results \
      --secure-environment-variables \
         AZURE_API_KEY="$AZURE_API_KEY" \
         AZURE_OPENAI_ENDPOINT="${AZURE_OPENAI_ENDPOINT:-}" \
         AZURE_OPENAI_API_VERSION="${AZURE_OPENAI_API_VERSION:-2024-12-01-preview}" \
         AZURE_AI_ENDPOINT="${AZURE_AI_ENDPOINT:-}" \
         LITELLM_HOST="${LITELLM_HOST:-}" \
         LITELLM_ILSP_EVAL_API_KEY="${LITELLM_ILSP_EVAL_API_KEY:-}" \
      --environment-variables MODEL="$m" DATASET="$ds" COND="$c" \
         OUTDIR=/results EXTRA="$EXTRA" \
      --command-line "bash deploy/run_fol_cell.sh" \
      --no-wait >/dev/null 2>&1
  then up=$((up+1)); echo "[$n/$total] launched $name"
  else bad=$((bad+1)); echo "[$n/$total] FAILED $name"; fi
done; done; done

echo
echo "launched $up, skipped $((n-up-bad)), failed $bad"
echo "Monitor: bash deploy/azure_status.sh"
