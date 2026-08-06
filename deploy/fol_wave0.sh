#!/usr/bin/env bash
# WAVE 0 -- repair the existing FOL data before anything is computed from it.
#
# Two defects found by analysis/audit.py:
#   1. fracas-multilabel__deepseek-r1__c1.json holds 2 items of 713 and
#      reports accuracy 0.000 over them. It did not error, it stopped. Any
#      mean taken over files is corrupted by it.
#   2. deepseek-r1 was never run on fracas-extended or oyxoy, so the grid
#      is 43 of 45 cells.
#
# The truncated file must be REMOVED, not resumed: --resume would keep its
# 2 items, and there is no way to tell whether they were written before or
# after whatever stopped the run.
set -uo pipefail
cd "$(dirname "$0")/.."

TRUNC="phase2_fol/results/fracas-multilabel/fracas-multilabel__deepseek-r1__c1.json"

echo "=== WAVE 0: FOL data repair ==="
if [ -f "$TRUNC" ]; then
  n=$(python3 -c "import json;print(len(json.load(open('$TRUNC'))['results']))" 2>/dev/null || echo '?')
  echo "Truncated file: $TRUNC"
  echo "  holds $n item(s) of 713"
  echo
  echo "It will be MOVED ASIDE (not deleted) to ${TRUNC}.truncated so the"
  echo "rerun starts clean and the original stays available for inspection."
  if [ "${YES:-0}" != "1" ]; then
    printf "Proceed? [y/N] "; read -r a
    case "$a" in y|Y) ;; *) echo aborted; exit 0;; esac
  fi
  mv "$TRUNC" "${TRUNC}.truncated"
  echo "  moved to ${TRUNC}.truncated"
else
  echo "no truncated file at $TRUNC (already repaired?)"
fi

echo
echo "Now launch the three repair cells (all deepseek-r1 / c1):"
echo
echo "  DATASETS='fracas-multilabel fracas-extended oyxoy' \\"
echo "  MODELS='deepseek-r1' CONDS='c1' \\"
echo "  bash deploy/azure_fol_fanout.sh"
echo
echo "1,476 + 713 = 2,189 items, roughly \$10."
echo "Gate: python analysis/audit.py must then report no 'truncated run'"
echo "and 45/45 FOL cells."
