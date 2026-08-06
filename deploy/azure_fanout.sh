#!/usr/bin/env bash
# Fan the grid out over Azure Container Instances: one container per
# (model x tier x condition) cell. 81 cells for the full Coq grid.
#
# Sequential on one machine the grid takes days (0.5s sleep + API latency
# x 27,702 items). One container per cell turns that into roughly the
# duration of a single cell, ~30-60 min.
set -euo pipefail
RG="${RG:-nestor-rg}"
LOC="${LOC:-westeurope}"
ACR="${ACR:?set ACR to your registry name, e.g. nestoracr}"
IMAGE="$ACR.azurecr.io/nestor:latest"
STORAGE="${STORAGE:?set STORAGE to your storage account name}"
SHARE="${SHARE:-nestor-results}"

MODELS="${MODELS:-gpt-4o gpt-5.4 deepseek-r1 deepseek-v4-pro grok-4-20 \
grok-4-20-reasoning llama-3.3-70b llama-4-maverick mistral-large-3}"
TIERS="${TIERS:-T0 T1 T2}"
CONDS="${CONDS:-c1 c2 c3}"

EXTRA="${EXTRA:-}"
PREFIX="${PREFIX:-}"
CPU="${CPU:-1}"
MEM="${MEM:-2}"
DATASET="${DATASET:-fracas}"

# --- preflight ---------------------------------------------------------
# Each mistake below would otherwise be discovered 81 containers later.
command -v az >/dev/null || { echo "FATAL: az CLI not installed"; exit 1; }
az account show >/dev/null 2>&1 || { echo "FATAL: not logged in -- run 'az login'"; exit 1; }
: "${AZURE_API_KEY:?FATAL: AZURE_API_KEY not exported (source your .env first)}"
: "${AZURE_OPENAI_ENDPOINT:?FATAL: AZURE_OPENAI_ENDPOINT not exported}"

if ! az acr repository show -n "$ACR" --image nestor:latest >/dev/null 2>&1; then
  echo "FATAL: $IMAGE not found in registry."
  echo "  Build it first:  az acr build -r $ACR -t nestor:latest -f deploy/Dockerfile ."
  exit 1
fi

KEY=$(az storage account keys list -g "$RG" -n "$STORAGE" --query "[0].value" -o tsv) \
  || { echo "FATAL: cannot read storage key for '$STORAGE' in '$RG'"; exit 1; }

# ACR admin credentials, needed for the container to pull the image.
ACR_USER=$(az acr credential show -n "$ACR" --query username -o tsv 2>/dev/null) || true
ACR_PASS=$(az acr credential show -n "$ACR" --query "passwords[0].value" -o tsv 2>/dev/null) || true
if [ -z "${ACR_USER:-}" ]; then
  echo "FATAL: could not read ACR credentials. Enable the admin user:"
  echo "  az acr update -n $ACR --admin-enabled true"
  exit 1
fi

count=0
for tier in $TIERS; do for cond in $CONDS; do for model in $MODELS; do
  count=$((count+1)); done; done; done
echo "About to launch $count containers (cpu=$CPU mem=${MEM}G each)."
echo "  models: $MODELS"
echo "  tiers:  $TIERS"
echo "  conds:  $CONDS"
echo "  extra:  ${EXTRA:-<none>}"
if [ "${YES:-0}" != "1" ]; then
  printf "Proceed? [y/N] "; read -r ans
  case "$ans" in y|Y) ;; *) echo "aborted"; exit 0;; esac
fi

n=0; launched=0; failed=0
for tier in $TIERS; do for cond in $CONDS; do for model in $MODELS; do
  # ACI names: lowercase alphanumeric and dashes only.
  #
  # The dataset must appear in the name or every dataset collides: the grid
  # is (model x tier x cond) per dataset, so oyxoy/gpt-4o/T0/c1 would
  # otherwise generate the same name as the fracas cell and be skipped by
  # the exists-check below -- launching nothing while appearing to succeed.
  # fracas is left unqualified so the 81 already-complete fracas cells keep
  # the names they were created with.
  dstag=""
  [ "$DATASET" != "fracas" ] && dstag="${DATASET}-"
  name="nestor-$(echo "${PREFIX}${dstag}${model}-${tier}-${cond}" \
        | tr '[:upper:]' '[:lower:]' | tr -c 'a-z0-9-' '-' \
        | sed 's/--*/-/g; s/^-//; s/-$//')"
  # ACI caps container-group names at 63 characters.
  if [ "${#name}" -gt 63 ]; then
    echo "FATAL: container name too long (${#name} > 63): $name" >&2
    exit 1
  fi
  n=$((n+1))
  if az container show -g "$RG" -n "$name" >/dev/null 2>&1; then
    echo "[$n/$count] exists, skipping: $name"
    continue
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
       AZURE_OPENAI_ENDPOINT="$AZURE_OPENAI_ENDPOINT" \
       AZURE_OPENAI_API_VERSION="${AZURE_OPENAI_API_VERSION:-2024-12-01-preview}" \
       AZURE_AI_ENDPOINT="${AZURE_AI_ENDPOINT:-}" \
       LITELLM_HOST="${LITELLM_HOST:-}" \
       LITELLM_ILSP_EVAL_API_KEY="${LITELLM_ILSP_EVAL_API_KEY:-}" \
       GPT_5_4_PRO_ENDPOINT="${GPT_5_4_PRO_ENDPOINT:-}" \
       GPT_5_4_PRO_API_KEY="${GPT_5_4_PRO_API_KEY:-}" \
    --environment-variables MODEL="$model" TIER="$tier" COND="$cond" \
       DATASET="$DATASET" OUTDIR=/results EXTRA="$EXTRA" PREFIX="$PREFIX" \
    --no-wait >/dev/null 2>&1
  then
    launched=$((launched+1)); echo "[$n/$count] launched $name"
  else
    failed=$((failed+1));  echo "[$n/$count] FAILED to launch $name"
  fi
done; done; done

echo
echo "launched $launched, skipped $((n-launched-failed)), failed $failed"
echo "results land on file share '$SHARE' (logs under logs/)"
echo
echo "Monitor:   bash deploy/azure_status.sh"
echo "Download:  az storage file download-batch --account-name $STORAGE \\"
echo "             --account-key '<key>' -s $SHARE -d phase2_coq/results"
