#!/usr/bin/env bash
# Pull results off the Azure file share, safely.
#
# Two hazards this handles:
#
#  1. PARTIAL LOCAL FILES. The local laptop run produced some cells that
#     stopped mid-way (e.g. 7 of 27 items). `download-batch` will not
#     necessarily overwrite them, so a partial file can survive and be
#     analysed as though it were a complete cell -- silently wrong, since
#     rates computed over 7 items are not comparable to 27. Any local file
#     with fewer items than the container's copy is moved aside first.
#
#  2. OVERWRITE SEMANTICS. Rather than relying on download-batch's overwrite
#     behaviour (which varies by az version and rejects --overwrite on some),
#     everything lands in an empty staging dir first and is then installed
#     deliberately, comparing item counts.
set -uo pipefail
cd "$(dirname "$0")/.."

RG="${RG:-nestor-rg}"
: "${STORAGE:?set STORAGE}"
SHARE="${SHARE:-nestor-results}"

KEY=$(az storage account keys list -g "$RG" -n "$STORAGE" --query "[0].value" -o tsv) \
  || { echo "FATAL: cannot read storage key"; exit 1; }

STAGE=".download_stage"
rm -rf "$STAGE"; mkdir -p "$STAGE"

echo "=== downloading share '$SHARE' to a staging dir first ==="
# --overwrite is not accepted by all az versions, and is unnecessary here:
# $STAGE is freshly created empty above, so nothing can be clobbered.
#
# download-batch can hit ResourceNotFound if a cell is still running: the
# pipelines write via temp-file + atomic rename, so a temp file can be listed
# and then renamed away before it is fetched. That is transient -- retry a
# few times; each retry re-lists and skips whatever already landed. If it
# still fails after the retries, real files did download (they are in $STAGE),
# so continue rather than abort: the count check below reports what arrived.
dl_ok=0
for attempt in 1 2 3; do
  if az storage file download-batch --account-name "$STORAGE" \
       --account-key "$KEY" -s "$SHARE" -d "$STAGE" >/dev/null 2>&1; then
    dl_ok=1; break
  fi
  echo "  download attempt $attempt hit a transient error (cell still writing?); retrying"
  sleep 10
done
[ "$dl_ok" -eq 1 ] || echo "  WARNING: download did not fully complete -- \
some cells may still be running. Installing what arrived; re-run later."

found=$(find "$STAGE" -name '*.json' | wc -l | tr -d ' ')
echo "  $found json file(s) downloaded"

# Compare item counts and install only what is not a regression.
python3 - "$STAGE" <<'PY'
import json, os, shutil, sys, glob
stage = sys.argv[1]

def count(p):
    # Count REAL items, not total. The install rule below KEEPs the local
    # file when it has MORE items than the remote (nd > ns). A stale
    # all-api_error file has 342 total items; a freshly-recomputed cell that
    # is still writing has fewer (say 105) at collect time. With len(results)
    # the stale file (342) > the fresh file (105), so KEEP-local fired and the
    # good remote file was never installed. Counting only non-api_error items
    # makes the stale file score 0 and the fresh file 105, so KEEP-local no
    # longer fires and the fresh file installs.
    try:
        d = json.load(open(p))
        r = d.get("results", d if isinstance(d, list) else [])
        return sum(1 for x in r if x.get("predicted_label") != "api_error")
    except Exception:
        return -1

installed = kept = moved = 0
for src in glob.glob(os.path.join(stage, "**", "*.json"), recursive=True):
    rel = os.path.relpath(src, stage)
    if rel.startswith("logs" + os.sep):
        continue
    # Coq cells live flat; FOL cells live under <dataset>/
    base = os.path.basename(src)
    if base.startswith("pilot__") or "__T" in base:
        dst = os.path.join("phase2_coq", "results", base)
    else:
        parts = rel.split(os.sep)
        dst = os.path.join("phase2_fol", "results", *parts[-2:]) \
            if len(parts) > 1 else os.path.join("phase2_fol", "results", base)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    ns, nd = count(src), (count(dst) if os.path.exists(dst) else -1)
    if nd > ns:
        print(f"  KEEP local ({nd} items > remote {ns}): {dst}")
        kept += 1
        continue
    if os.path.exists(dst) and nd < ns:
        shutil.move(dst, dst + f".partial{nd}")
        print(f"  moved aside local partial ({nd} items): {dst}")
        moved += 1
    shutil.copy2(src, dst)
    installed += 1

print(f"\ninstalled {installed}, kept-local {kept}, moved-aside {moved}")
PY

# Logs are worth keeping: container logs vanish with the instance.
if [ -d "$STAGE/logs" ]; then
  mkdir -p logs/container
  cp -f "$STAGE"/logs/* logs/container/ 2>/dev/null
  echo "  container logs -> logs/container/"
fi

rm -rf "$STAGE"
echo
echo "Now: python analysis/coq_analysis.py && python analysis/fol_analysis.py"
echo "     python analysis/audit.py && python analysis/make_paper.py"
