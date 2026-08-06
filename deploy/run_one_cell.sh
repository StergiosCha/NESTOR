#!/usr/bin/env bash
# One (model x tier x condition) cell -- the unit of parallelism. Each cell
# writes its own file, so cells are independent and the grid can fan out
# over Azure Container Instances.
#
# Everything here is about surviving unattended execution: the caller is
# asleep, so a cell must either produce a complete result file or leave
# enough evidence to say why it did not.
set -uo pipefail

: "${MODEL:?set MODEL}" ; : "${TIER:?set TIER}" ; : "${COND:?set COND}"
DATASET="${DATASET:-fracas}"
DATA="${DATA:-data/fracas/fracas.xml}"
OUTDIR="${OUTDIR:-/results}"
EXTRA="${EXTRA:-}"
PREFIX="${PREFIX:-}"
ATTEMPTS="${CELL_ATTEMPTS:-3}"

# `python` is not guaranteed to exist as a bare name; python3 always is on
# the slim images. Resolve once so both the item counter and the pipeline
# invocation use the same interpreter.
PY_BIN="${PY_BIN:-}"
if [ -z "$PY_BIN" ]; then
  if command -v python3 >/dev/null; then PY_BIN=python3
  elif command -v python >/dev/null; then PY_BIN=python
  else echo "FATAL: no python interpreter on PATH"; exit 78; fi
fi

mkdir -p "$OUTDIR"
OUT="$OUTDIR/${PREFIX}${DATASET}__${MODEL}__${TIER}__${COND}.json"
LOG="$OUTDIR/logs/${PREFIX}${DATASET}__${MODEL}__${TIER}__${COND}.log"
mkdir -p "$(dirname "$LOG")"

# Mirror stdout/stderr into a log on the shared volume. Container logs
# vanish when the instance is deleted; the run must remain diagnosable
# afterwards.
exec > >(tee -a "$LOG") 2>&1

echo "=== cell $MODEL / $TIER / $COND @ $(date -u +%FT%TZ) ==="

# --- preflight: fail loudly and immediately, not 27 items later --------
if ! command -v coqc >/dev/null; then
  echo "FATAL: coqc not on PATH"; exit 78
fi
echo "coqc: $(coqc --version | head -1)"
if [ -z "${AZURE_API_KEY:-}" ]; then
  echo "FATAL: AZURE_API_KEY empty -- every item would fail identically"
  exit 78
fi
if [ ! -f "$DATA" ]; then
  echo "FATAL: dataset not found at $DATA"; exit 78
fi

# Is this cell already complete? The pipeline resumes within a partially
# written file, so only a cell whose item count matches the request is
# genuinely done.
completed_items() {
  [ -f "$OUT" ] || { echo 0; return; }
  "$PY_BIN" - "$OUT" <<'PY' 2>/dev/null || echo 0
import json,sys
try:
    d=json.load(open(sys.argv[1]))
    rs=d.get("results",d if isinstance(d,list) else [])
    print(sum(1 for r in rs if r.get("predicted_label")!="api_error"))
except Exception:
    print(0)
PY
}

before=$(completed_items)
if [ "$before" -gt 0 ]; then
  echo "resuming: $before item(s) already in $OUT"
fi

# --- run, with retries -------------------------------------------------
# A cell can die on a transient Azure fault. Because the pipeline writes
# after every item and resumes from what is on disk, re-invoking it costs
# only the items still missing -- so retrying is cheap and never
# duplicates work.
rc=1
for attempt in $(seq 1 "$ATTEMPTS"); do
  echo "--- attempt $attempt/$ATTEMPTS ---"
  "$PY_BIN" phase2_coq/coq_pipeline.py \
    --data "$DATA" --dataset "$DATASET" \
    --model "$MODEL" --tier "$TIER" --condition "$COND" \
    --output "$OUT" $EXTRA
  rc=$?
  [ "$rc" -eq 0 ] && break
  after=$(completed_items)
  echo "attempt $attempt exited $rc (items on disk: $after)"
  if [ "$attempt" -lt "$ATTEMPTS" ]; then
    backoff=$((attempt * 60))
    echo "sleeping ${backoff}s before retry"
    sleep "$backoff"
  fi
done

final=$(completed_items)
echo "=== cell finished rc=$rc items=$final @ $(date -u +%FT%TZ) ==="
if [ "$rc" -ne 0 ] && [ "$final" -eq 0 ]; then
  echo "CELL FAILED with no results -- see $LOG"
  exit "$rc"
fi
exit 0
