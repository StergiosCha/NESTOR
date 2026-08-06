#!/usr/bin/env bash
# Phase 2b Coq pilot: 3 tiers x 2 conditions x 3 models x 27 stratified items
# = 486 generations, $7.28. This is the gate that decides whether the full
# $415.72 grid is worth running (see RUN_ALL.md wave 1).
set -euo pipefail
cd "$(dirname "$0")"

# --- credentials -------------------------------------------------------
if [ -f .env ]; then set -a; . ./.env; set +a; fi
if [ -z "${AZURE_API_KEY:-}" ]; then
  echo "ERROR: AZURE_API_KEY is empty."
  echo "Put your key in the AZURE_API_KEY= line of .env, then re-run."
  exit 1
fi

# --- coq ---------------------------------------------------------------
if [ -z "${COQC_PATH:-}" ] || [ "${COQC_PATH}" = "coqc" ]; then
  if [ -x "./coq812/bin/coqc" ]; then
    export OCAMLLIB="$PWD/coq812/lib/ocaml"
    export COQC_PATH="$PWD/coq812/bin/coqc"
  fi
fi
echo "coqc: $($COQC_PATH --version 2>&1 | head -1)"

MODELS="${MODELS:-gpt-5.4 grok-4-20-reasoning llama-3.3-70b}"
TIERS="${TIERS:-T0 T1 T2}"
CONDS="${CONDS:-c1 c3}"
PER_SECTION="${PER_SECTION:-3}"

mkdir -p phase2_coq/results
n=0
for tier in $TIERS; do for cond in $CONDS; do for model in $MODELS; do
  out="phase2_coq/results/pilot__fracas__${model}__${tier}__${cond}.json"
  n=$((n+1))
  if [ -f "$out" ]; then echo "[$n] skip (exists): $(basename "$out")"; continue; fi
  echo "[$n] $model / $tier / $cond"
  python phase2_coq/coq_pipeline.py \
    --data data/fracas/fracas.xml --dataset fracas \
    --model "$model" --tier "$tier" --condition "$cond" \
    --stratified "$PER_SECTION" --seed 0 \
    --output "$out"
done; done; done

echo
echo "=== analysing ==="
python analysis/coq_analysis.py
python analysis/audit.py
