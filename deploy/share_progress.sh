#!/usr/bin/env bash
# What is on the share right now, per cell, recursing into dataset dirs.
# Reads only; downloads nothing. Byte size is the progress signal -- a
# growing file is a cell mid-run, since the pipelines write per item.
set -uo pipefail
RG="${RG:-nestor-rg}"; : "${STORAGE:?set STORAGE}"; SHARE="${SHARE:-nestor-results}"
KEY=$(az storage account keys list -g "$RG" -n "$STORAGE" --query "[0].value" -o tsv) \
  || { echo "cannot read storage key"; exit 1; }

# --recursive lists the whole tree; older az versions lack it, so fall back
# to walking the known dataset subdirectories.
if az storage file list --account-name "$STORAGE" --account-key "$KEY" \
     -s "$SHARE" --recursive -o tsv >/dev/null 2>&1; then
  az storage file list --account-name "$STORAGE" --account-key "$KEY" \
    -s "$SHARE" --recursive \
    --query "[?properties.contentLength!=null].{n:name,s:properties.contentLength}" \
    -o tsv 2>/dev/null | sort | awk '{printf "  %-62s %9s B\n",$1,$2}'
else
  az storage file list --account-name "$STORAGE" --account-key "$KEY" -s "$SHARE" \
    --query "[?properties.contentLength!=null].{n:name,s:properties.contentLength}" \
    -o tsv 2>/dev/null | sort | awk '{printf "  %-62s %9s B\n",$1,$2}'
  for d in fracas fracas-translated fracas-extended fracas-multilabel oyxoy logs; do
    az storage file list --account-name "$STORAGE" --account-key "$KEY" \
      -s "$SHARE" -p "$d" \
      --query "[?properties.contentLength!=null].{n:name,s:properties.contentLength}" \
      -o tsv 2>/dev/null | sort | awk -v d="$d" '{printf "  %-62s %9s B\n",d"/"$1,$2}'
  done
fi
