#!/usr/bin/env bash
# Drive the Coq grid to completion, hands-off.
#
# Each pass: find every incomplete cell (items < 342 OR any api_error),
# delete its container, relaunch the whole grid (complete cells are skipped
# because their containers still exist), wait for a STABLE zero running,
# download (real-item count means a short remote never clobbers a fuller
# local), and re-check. Repeat until all 81 are complete or MAX_PASSES.
#
# Converges because the pipeline resumes from the share and writes per item:
# every pass is additive -- slow reasoning-model cells that truncate gain
# items each pass, rate-limited llama items are re-attempted each pass.
set -uo pipefail
cd "$(dirname "$0")"
set -a; . ./.env; set +a

MODELS="gpt-4o gpt-5.4 deepseek-r1 deepseek-v4-pro grok-4-20 grok-4-20-reasoning llama-3.3-70b llama-4-maverick mistral-large-3"
MAX_PASSES="${MAX_PASSES:-10}"
POLL="${POLL:-120}"
STABLE_CHECKS="${STABLE_CHECKS:-2}"

scorecard() {
  python3 - <<'PY'
import json,glob,os,sys
def info(f):
    try:
        d=json.load(open(f)); r=d.get("results",[])
        return len(r), sum(1 for x in r if x.get("predicted_label")=="api_error")
    except Exception: return 0,0
grid=[f for f in glob.glob("phase2_coq/results/*.json") if not any(x in f for x in("krikri","pilot__","harness"))]
per={c:0 for c in("c1","c2","c3")}
for f in grid:
    c=os.path.basename(f).split("__")[-1].replace(".json","")
    t,a=info(f)
    if t>=342 and a==0 and c in per: per[c]+=1
ok=sum(per.values())
print(f"  c1 {per['c1']}/27  c2 {per['c2']}/27  c3 {per['c3']}/27   TOTAL {ok}/81")
sys.exit(0 if ok>=81 else 1)
PY
}

incomplete_to_file() {
  python3 - "$1" <<'PY'
import json,glob,os,re,sys
def info(f):
    try:
        d=json.load(open(f)); r=d.get("results",[])
        return len(r), sum(1 for x in r if x.get("predicted_label")=="api_error")
    except Exception: return 0,0
grid=[f for f in glob.glob("phase2_coq/results/*.json") if not any(x in f for x in("krikri","pilot__","harness"))]
out=open(sys.argv[1],"w")
for f in grid:
    t,a=info(f)
    if t<342 or a>0:
        _,m,ti,c=os.path.basename(f).replace(".json","").split("__")
        out.write(re.sub(r'-+','-',f"nestor-{m}-{ti}-{c}".lower().replace(".","-").replace("_","-"))+"\n")
out.close()
PY
}

running_count() {
  az container list -g "$RG" \
    --query "length([?instanceView.state=='Running'])" -o tsv 2>/dev/null || echo 999
}

for pass in $(seq 1 "$MAX_PASSES"); do
  echo "========================================================"
  echo "PASS $pass/$MAX_PASSES  @ $(date -u +%FT%TZ)"
  echo "========================================================"

  if scorecard; then echo "ALL 81 COMPLETE"; break; fi

  incomplete_to_file /tmp/nestor_bad.txt
  n=$(wc -l < /tmp/nestor_bad.txt | tr -d ' ')
  echo "  incomplete cells: $n"
  [ "$n" -eq 0 ] && { echo "  nothing incomplete"; break; }

  while read -r c; do
    [ -n "$c" ] && az container delete -g "$RG" -n "$c" --yes >/dev/null 2>&1 &
  done < /tmp/nestor_bad.txt
  wait
  echo "  deleted $n containers"

  MODELS="$MODELS" TIERS="T0 T1 T2" CONDS="c1 c2 c3" YES=1 \
    bash deploy/azure_fanout.sh >/dev/null 2>&1
  echo "  relaunched grid"

  zeros=0
  while :; do
    sleep "$POLL"
    r=$(running_count)
    echo "    running=$r  @ $(date -u +%T)"
    if [ "$r" = "0" ]; then
      zeros=$((zeros+1))
      [ "$zeros" -ge "$STABLE_CHECKS" ] && break
    else
      zeros=0
    fi
  done

  echo "  collecting..."
  bash deploy/download_results.sh >/dev/null 2>&1
  scorecard || true
done

echo
echo "=== FINAL SCORECARD ==="
scorecard || true
echo "Now finalize:  ./GO.sh --finish"
