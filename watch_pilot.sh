#!/usr/bin/env bash
# Live progress for the Coq pilot / full grid.
# macOS has no `watch`, so this is a plain refresh loop. Ctrl-C to stop --
# it only reads files, so stopping it never touches the run.
#
#   ./watch_pilot.sh            # refresh every 30s
#   ./watch_pilot.sh 10         # every 10s
#   ./watch_pilot.sh 0          # print once and exit
cd "$(dirname "$0")"
INTERVAL="${1:-30}"

render() {
  printf '\n=== Coq run progress — %s ===\n' "$(date '+%H:%M:%S')"
  python3 - <<'PY'
import glob, json, os
files = sorted(glob.glob("phase2_coq/results/pilot__*.json")) \
      + sorted(glob.glob("phase2_coq/results/fracas__*.json"))
if not files:
    print("  no result files yet — the first cell is still on its first item")
    raise SystemExit
tot = comp = corr = prov = 0
print(f"  {'cell':<44}{'items':>6}{'compiled':>10}{'proved':>8}{'correct':>9}")
print("  " + "-" * 77)
for f in files:
    try:
        with open(f) as fh:
            d = json.load(fh)
    except (json.JSONDecodeError, OSError):
        print(f"  {os.path.basename(f)[:44]:<44}{'(writing…)':>33}")
        continue
    s = d.get("summary", {})
    n = s.get("total", 0)
    name = os.path.basename(f).replace("pilot__fracas__", "").replace(".json", "")
    print(f"  {name[:44]:<44}{n:>6}{s.get('compiled',0):>10}"
          f"{s.get('proof_complete',0):>8}{s.get('correct',0):>9}")
    tot += n; comp += s.get("compiled", 0)
    prov += s.get("proof_complete", 0); corr += s.get("correct", 0)
if tot:
    print("  " + "-" * 77)
    print(f"  {'TOTAL':<44}{tot:>6}{comp:>10}{prov:>8}{corr:>9}")
    print(f"\n  compiled {comp/tot:.1%} | proof complete {prov/tot:.1%} "
          f"| correct {corr/tot:.1%}")
    print(f"  cells done: {len(files)}/18")
PY
  if ls phase2_coq/results/*.tmp >/dev/null 2>&1; then
    echo "  (a cell is mid-write — normal)"
  fi
}

if [ "$INTERVAL" = "0" ]; then render; exit 0; fi
while true; do clear; render; sleep "$INTERVAL"; done
