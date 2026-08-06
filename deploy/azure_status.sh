#!/usr/bin/env bash
# Status of every nestor-* container instance, plus what each one has
# written so far. Read-only: safe to run at any time.
#
#   bash deploy/azure_status.sh          # one snapshot
#   bash deploy/azure_status.sh -w       # refresh every 60s
#   bash deploy/azure_status.sh -l NAME  # tail one container's log
set -uo pipefail
RG="${RG:-nestor-rg}"

if [ "${1:-}" = "-l" ]; then
  : "${2:?usage: azure_status.sh -l <container-name>}"
  az container logs -g "$RG" -n "$2"
  exit 0
fi

snapshot() {
  echo "=== nestor containers in $RG @ $(date -u +%FT%TZ) ==="
  # `az container list` does NOT populate instanceView -- every state comes
  # back null. provisioningState IS populated in list view and is enough to
  # tell Succeeded/Failed/Running apart, so use it as the primary signal and
  # fall back to a per-container show only for the ones still in flight.
  az container list -g "$RG" \
    --query "[?starts_with(name,'nestor-')].{name:name,state:provisioningState}" \
    -o tsv 2>/dev/null | sort | awk '
      { printf "  %-46s %s\n", $1, $2; st[$2]++ }
      END { printf "\n  "; for (s in st) printf "%s=%d  ", s, st[s]; printf "\n" }'

  # Real run state (Running / Terminated / Waiting) needs `show` per
  # container. Only worth it for a handful, so summarise counts.
  echo
  echo "  container run states (from az container show):"
  names=$(az container list -g "$RG" \
    --query "[?starts_with(name,'nestor-')].name" -o tsv 2>/dev/null)
  : > /tmp/.nestor_states
  for n in $names; do
    # Two places carry state; instanceView.state is the group-level one and
    # containers[0]...currentState.state the per-container one. Try both, and
    # capture the exit code so a crash-on-start is distinguishable from a
    # clean finish -- provisioningState says "Succeeded" for both.
    read -r st code <<< "$(az container show -g "$RG" -n "$n" --query \
      "[instanceView.state, containers[0].instanceView.currentState.exitCode]" \
      -o tsv 2>/dev/null)"
    echo "${st:-Unknown} exit=${code:-?}" >> /tmp/.nestor_states
  done
  sort /tmp/.nestor_states | uniq -c | awk '{printf "    %-14s %s\n", $2, $1}'
  rm -f /tmp/.nestor_states

  echo
  echo "  Terminated containers still cost nothing but hold the name."
  echo "  Failed cells:  az container logs -g $RG -n <name>"
  echo "  Cleanup:       bash deploy/azure_cleanup.sh"
}

if [ "${1:-}" = "-w" ]; then
  while true; do clear; snapshot; sleep "${2:-60}"; done
else
  snapshot
fi
