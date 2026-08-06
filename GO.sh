#!/usr/bin/env bash
# ONE BUTTON. Launch everything, wait, collect, analyse, write the paper.
#
#   ./GO.sh              # full run: pilot + FOL waves, then wait and finish
#   ./GO.sh --collect    # skip launching; just wait for what is already up
#   ./GO.sh --finish     # skip waiting; collect + analyse what exists now
#   ./GO.sh --full-grid  # after a passing pilot: the 81-cell Coq grid
#
# Safe to re-run and safe to Ctrl-C: every stage skips work already done,
# containers resume from what is on the share, and nothing is deleted
# until results are on disk and verified.
#
# Needs, in the environment or .env:
#   RG LOC ACR STORAGE   (Azure) and AZURE_API_KEY (+ endpoints)
set -uo pipefail
cd "$(dirname "$0")"

MODE="${1:-run}"
POLL="${POLL:-120}"          # seconds between status checks
MAX_WAIT="${MAX_WAIT:-86400}" # give up waiting after 24h
LOG="run_$(date -u +%Y%m%dT%H%M%SZ).log"
exec > >(tee -a "$LOG") 2>&1

say() { printf '\n\033[1m=== %s ===\033[0m %s\n' "$1" "$(date -u +%FT%TZ)"; }
die() { echo "FATAL: $*"; exit 1; }

# ---------------------------------------------------------------- preflight
say "PREFLIGHT"
[ -f .env ] && { set -a; . ./.env; set +a; echo "loaded .env"; }
: "${AZURE_API_KEY:?AZURE_API_KEY not set (put it in .env)}"
: "${ACR:?ACR not set}" ; : "${STORAGE:?STORAGE not set}"
RG="${RG:-nestor-rg}"; LOC="${LOC:-westeurope}"; SHARE="${SHARE:-nestor-results}"
export RG LOC ACR STORAGE SHARE
command -v az >/dev/null || die "az CLI not installed"
az account show >/dev/null 2>&1 || die "not logged in; run 'az login'"
az acr repository show -n "$ACR" --image nestor:latest >/dev/null 2>&1 \
  || die "image not in registry; run: az acr build -r $ACR -t nestor:latest -f deploy/Dockerfile ."
echo "RG=$RG  ACR=$ACR  STORAGE=$STORAGE  SHARE=$SHARE"
echo "log: $LOG"

# ------------------------------------------------------------------- launch
if [ "$MODE" = "run" ] || [ "$MODE" = "--full-grid" ]; then
  say "LAUNCH"
  export YES=1   # non-interactive: this script is the confirmation

  if [ "$MODE" = "--full-grid" ]; then
    echo "Coq FULL GRID: 9 models x 3 tiers x 3 conditions x 342 items"
    MODELS="gpt-4o gpt-5.4 deepseek-r1 deepseek-v4-pro grok-4-20 \
grok-4-20-reasoning llama-3.3-70b llama-4-maverick mistral-large-3" \
      TIERS="T0 T1 T2" CONDS="c1 c2 c3" bash deploy/azure_fanout.sh
  else
    echo "Coq pilot: 3 models x 3 tiers x 2 conditions x 27 stratified items"
    MODELS="gpt-5.4 grok-4-20-reasoning llama-3.3-70b" \
      TIERS="T0 T1 T2" CONDS="c1 c3" \
      EXTRA="--stratified 3 --seed 0" PREFIX="pilot__" \
      bash deploy/azure_fanout.sh

    # FOL wave 0: move the truncated file aside, then rerun + backfill.
    TRUNC="phase2_fol/results/fracas-multilabel/fracas-multilabel__deepseek-r1__c1.json"
    [ -f "$TRUNC" ] && { mv "$TRUNC" "$TRUNC.truncated"; echo "moved aside $TRUNC"; }
    echo "FOL wave 0: repair + backfill (deepseek-r1, c1)"
    DATASETS="fracas-multilabel fracas-extended oyxoy" MODELS="deepseek-r1" \
      CONDS="c1" bash deploy/azure_fol_fanout.sh

    echo "FOL c3: gold-label condition, FraCaS x 9 models"
    DATASETS="fracas" CONDS="c3" bash deploy/azure_fol_fanout.sh
  fi
  unset YES
fi

# --------------------------------------------------------------------- wait
if [ "$MODE" != "--finish" ]; then
  say "WAIT"
  echo "polling every ${POLL}s, giving up after $((MAX_WAIT/3600))h"
  waited=0
  while [ "$waited" -lt "$MAX_WAIT" ]; do
    states=$(az container list -g "$RG" \
      --query "[?starts_with(name,'nestor-')].instanceView.state" -o tsv 2>/dev/null)
    [ -z "$states" ] && { echo "no nestor containers found"; break; }
    tot=$(echo "$states" | wc -l | tr -d ' ')
    run=$(echo "$states" | grep -cE 'Running|Pending|Waiting' || true)
    ok=$(echo "$states"  | grep -c 'Succeeded' || true)
    bad=$(echo "$states" | grep -c 'Failed' || true)
    printf '  %s  total=%s running=%s succeeded=%s failed=%s\n' \
      "$(date -u +%H:%M:%SZ)" "$tot" "$run" "$ok" "$bad"
    [ "$run" -eq 0 ] && { echo "  all containers terminal"; break; }
    sleep "$POLL"; waited=$((waited+POLL))
  done
  [ "$waited" -ge "$MAX_WAIT" ] && echo "WARNING: wait timed out; collecting what exists"
fi

# ------------------------------------------------------------------ collect
say "COLLECT"
bash deploy/download_results.sh || die "download failed"

# ------------------------------------------------------------------ analyse
say "ANALYSE"
ok=1
for s in phase1_tables judge_analysis fol_analysis agreement coq_analysis \
         cross_pipeline audit; do
  printf '  %-18s ' "$s"
  if python analysis/$s.py >/dev/null 2>&1; then echo OK
  else echo FAILED; ok=0; fi
done
[ "$ok" -eq 1 ] || echo "  (one or more scripts failed -- see below)"

say "PAPER"
python analysis/make_paper.py || die "paper generation failed"

# ------------------------------------------------------------------- report
say "RESULTS"
./watch_pilot.sh 0 2>/dev/null || true

echo
echo "--- Coq by tier ---"
[ -s analysis/tables/coq_by_tier.csv ] && column -s, -t < analysis/tables/coq_by_tier.csv \
  || echo "  (no Coq results)"

echo
echo "--- FOL by condition ---"
python3 - <<'PY'
import glob, json, collections
agg = collections.defaultdict(lambda: [0, 0])
for p in glob.glob("phase2_fol/results/*/*.json"):
    try:
        d = json.load(open(p))
    except Exception:
        continue
    c = (d.get("metadata") or {}).get("condition", "?")
    s = d.get("summary") or {}
    agg[c][0] += s.get("success_count", 0)
    agg[c][1] += s.get("total", 0)
for c in sorted(agg):
    hit, tot = agg[c]
    print(f"  {c}: {hit}/{tot} = {hit/tot:.1%}" if tot else f"  {c}: no items")
PY

echo
echo "--- defects the audit found ---"
[ -s analysis/tables/audit_defects.csv ] && column -s, -t < analysis/tables/audit_defects.csv \
  || echo "  (none)"

say "DONE"
echo "paper:   paper/nestor.md   paper/nestor.tex"
echo "tables:  analysis/tables/  ($(ls analysis/tables/*.csv 2>/dev/null | wc -l | tr -d ' ') csv)"
echo "figures: analysis/figs/    ($(ls analysis/figs/*.png 2>/dev/null | wc -l | tr -d ' ') png)"
echo "log:     $LOG"
echo
echo "Containers are NOT deleted -- results are downloaded but verify first, then:"
echo "  bash deploy/azure_cleanup.sh"
echo "  az group delete -n $RG --yes    # removes everything including storage"
