#!/usr/bin/env bash
# One FOL (dataset x model x condition) cell. Mirrors run_one_cell.sh:
# preflight loudly, log to the shared volume, retry with backoff, and let
# the pipeline's own --resume pick up a partially completed file.
set -uo pipefail

: "${MODEL:?set MODEL}" ; : "${DATASET:?set DATASET}"
COND="${COND:-c1}"
OUTDIR="${OUTDIR:-/results}"
EXTRA="${EXTRA:-}"
ATTEMPTS="${CELL_ATTEMPTS:-3}"

PY_BIN="${PY_BIN:-}"
if [ -z "$PY_BIN" ]; then
  if command -v python3 >/dev/null; then PY_BIN=python3
  elif command -v python >/dev/null; then PY_BIN=python
  else echo "FATAL: no python interpreter on PATH"; exit 78; fi
fi

mkdir -p "$OUTDIR/$DATASET" "$OUTDIR/logs"
OUT="$OUTDIR/$DATASET/${DATASET}__${MODEL}__${COND}.json"
LOG="$OUTDIR/logs/fol__${DATASET}__${MODEL}__${COND}.log"
exec > >(tee -a "$LOG") 2>&1

echo "=== FOL cell $DATASET / $MODEL / $COND @ $(date -u +%FT%TZ) ==="

# --- preflight ---------------------------------------------------------
for bin in prover9 mace4; do
  command -v "$bin" >/dev/null || { echo "FATAL: $bin not on PATH"; exit 78; }
done
echo "prover9: $(command -v prover9)   mace4: $(command -v mace4)"
[ -n "${AZURE_API_KEY:-}" ] || { echo "FATAL: AZURE_API_KEY empty"; exit 78; }

# c2/c4 read this model's own Phase 1 answers; without that file the run
# would either crash per item or silently formalise with "unknown".
if [ "$COND" = "c2" ] || [ "$COND" = "c4" ]; then
  P1="phase1_nli_eval/results/${DATASET}/${DATASET}__${MODEL}__zero-shot__en.json"
  [ -f "$P1" ] || { echo "FATAL: condition $COND needs $P1 (not in image)"; exit 78; }
  echo "phase1 source: $P1"
fi

count_items() {
  [ -f "$OUT" ] || { echo 0; return; }
  "$PY_BIN" - "$OUT" <<'PY' 2>/dev/null || echo 0
import json,sys
try:
    d=json.load(open(sys.argv[1]))
    print(len(d.get("results", d if isinstance(d,list) else [])))
except Exception:
    print(0)
PY
}

before=$(count_items)
[ "$before" -gt 0 ] && echo "found $before existing item(s); --resume will continue"

rc=1
for attempt in $(seq 1 "$ATTEMPTS"); do
  echo "--- attempt $attempt/$ATTEMPTS ---"
  "$PY_BIN" phase2_fol/fol_pipeline.py \
    --data "$DATASET" --model "$MODEL" --condition "$COND" \
    --output "$OUT" --resume $EXTRA
  rc=$?
  [ "$rc" -eq 0 ] && break
  echo "attempt $attempt exited $rc (items: $(count_items))"
  [ "$attempt" -lt "$ATTEMPTS" ] && { s=$((attempt*60)); echo "sleep ${s}s"; sleep "$s"; }
done

final=$(count_items)
echo "=== FOL cell done rc=$rc items=$final @ $(date -u +%FT%TZ) ==="
[ "$rc" -ne 0 ] && [ "$final" -eq 0 ] && exit "$rc"
exit 0
