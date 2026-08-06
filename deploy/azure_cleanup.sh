#!/usr/bin/env bash
# Delete finished nestor-* container instances.
#
# Only containers in a terminal state are removed, and never before their
# results have been downloaded -- deleting a Running container throws away
# the items it has not written yet. Deletion is irreversible, so this
# always lists what it will remove and asks first (YES=1 to skip).
#
#   bash deploy/azure_cleanup.sh          # terminated only
#   ALL=1 bash deploy/azure_cleanup.sh    # running ones too (asks again)
set -uo pipefail
RG="${RG:-nestor-rg}"

mapfile -t rows < <(az container list -g "$RG" \
  --query "[?starts_with(name,'nestor-')].[name,instanceView.state]" -o tsv 2>/dev/null)

if [ "${#rows[@]}" -eq 0 ]; then echo "no nestor-* containers in $RG"; exit 0; fi

targets=(); running=()
for r in "${rows[@]}"; do
  name=$(echo "$r" | cut -f1); state=$(echo "$r" | cut -f2)
  case "$state" in
    Succeeded|Failed|Terminated) targets+=("$name") ;;
    *) running+=("$name $state") ;;
  esac
done

if [ "${#running[@]}" -gt 0 ]; then
  echo "STILL RUNNING (not deleted unless ALL=1):"
  printf '  %s\n' "${running[@]}"
  echo
fi

if [ "${ALL:-0}" = "1" ] && [ "${#running[@]}" -gt 0 ]; then
  echo "ALL=1: running containers will ALSO be deleted."
  echo "Any items they have not yet written to the share will be LOST."
  printf "Type 'delete-running' to confirm: "; read -r c
  if [ "$c" = "delete-running" ]; then
    for r in "${running[@]}"; do targets+=("$(echo "$r" | cut -d' ' -f1)"); done
  else
    echo "keeping running containers"
  fi
fi

if [ "${#targets[@]}" -eq 0 ]; then echo "nothing to delete"; exit 0; fi

echo "Will DELETE ${#targets[@]} container(s):"
printf '  %s\n' "${targets[@]}"
echo
echo "Confirm your results are downloaded first:"
echo "  az storage file download-batch --account-name <acct> -s nestor-results -d phase2_coq/results"
echo
if [ "${YES:-0}" != "1" ]; then
  printf "Proceed? [y/N] "; read -r ans
  case "$ans" in y|Y) ;; *) echo "aborted"; exit 0;; esac
fi

for t in "${targets[@]}"; do
  az container delete -g "$RG" -n "$t" --yes >/dev/null 2>&1 \
    && echo "  deleted $t" || echo "  FAILED to delete $t"
done
