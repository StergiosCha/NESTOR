#!/usr/bin/env bash
# One command: collect from the share, then print exactly what is missing.
set -euo pipefail
cd "$(dirname "$0")"
set -a; . ./.env; set +a

echo "=== 1/2 collecting from share ==="
bash deploy/download_results.sh 2>&1 | tail -3

echo
echo "=== 2/2 what is missing ==="
python3 - <<'PY'
import json,glob,os,time
SIZE={"fracas":342,"fracas-translated":342,"fracas-extended":427,"fracas-multilabel":713,"oyxoy":1049}
MODELS="gpt-4o gpt-5.4 deepseek-r1 deepseek-v4-pro grok-4-20 grok-4-20-reasoning llama-3.3-70b llama-4-maverick mistral-large-3".split()

short=[]; agg={}
for f in glob.glob("phase2_coq/results/*.json"):
    b=os.path.basename(f)
    if "pilot__" in b or "krikri" in b: continue
    ds=b.split("__")[0]; exp=SIZE.get(ds,0)
    try: rs=json.load(open(f)).get("results",[])
    except Exception: continue
    ae=sum(1 for r in rs if r.get("predicted_label")=="api_error")
    good=len(rs)-ae
    a=agg.setdefault(ds,[0,0,0]); a[0]+=1; a[1]+=good
    if good>=exp*0.99: a[2]+=1
    else: short.append((ds,b.split("__")[1],b.split("__")[3].replace(".json",""),good,exp,ae))

print("COQ")
ti=tw=0
for ds in sorted(agg):
    c,good,full=agg[ds]; exp=SIZE[ds]; nc=81 if ds=="fracas" else 27
    want=exp*nc; ti+=good; tw+=want
    print(f"  {ds:20} {full:3}/{nc} cells  {good:7,}/{want:,} ({100*good/want:5.1f}%)")
print(f"  {'TOTAL':20}          {ti:,}/{tw:,} ({100*ti/tw:.1f}%)")

print(f"\nCOQ CELLS SHORT: {len(short)}")
for ds,m,c,g,exp,ae in sorted(short):
    print(f"  {ds:18} {m:22} {c}  {g:5}/{exp}  missing {exp-g:4}  (api_err {ae})")

print("\nFOL")
folshort=[]
for cond in ("c1","c2","c3"):
    full=items=want=0
    for ds,exp in SIZE.items():
        for m in MODELS:
            want+=exp
            p=f"phase2_fol/results/{ds}/{ds}__{m}__{cond}.json"
            t=0
            if os.path.exists(p):
                try: t=json.load(open(p)).get("summary",{}).get("total",0)
                except Exception: t=0
            items+=t
            if t<exp*0.99: folshort.append((ds,m,cond,t,exp))
            else: full+=1
    print(f"  {cond}: {full}/45 cells  {items:,}/{want:,} ({100*items/want:5.1f}%)")
for ds,m,c,t,exp in folshort:
    print(f"  SHORT {ds}/{m}/{c}  {t}/{exp}  missing {exp-t}")

print(f"\nMISSING COQ ITEMS: {sum(exp-g for _,_,_,g,exp,_ in short):,}")
print(f"MISSING FOL ITEMS: {sum(exp-t for _,_,_,t,exp in folshort):,}")
PY
