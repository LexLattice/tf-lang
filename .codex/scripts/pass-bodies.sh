#!/usr/bin/env bash
# DEPRECATION: prefer pack-pass + pass-report; scheduled removal after v0.3
set -euo pipefail
[[ $# -ge 2 ]] || { echo "Usage: pass-bodies.sh <GROUP> <PR|PR-PR|PR[:LABEL]>..."; exit 2; }
GROUP="$1"; shift
command -v gh >/dev/null || { echo "Requires GitHub CLI: gh"; exit 1; }

# expand ranges & normalize
TOK=("$@"); EXP=()
for t in "${TOK[@]}"; do
  if [[ "$t" =~ ^([0-9]+)-([0-9]+)$ ]]; then s=${BASH_REMATCH[1]}; e=${BASH_REMATCH[2]}; ((e<s))&&{tmp=$s;s=$e;e=$tmp;}
    for ((i=s;i<=e;i++));do EXP+=("$i");done
  else EXP+=("$t"); fi
done

# map to labels A/B/C/D if not provided
alpha=({A..Z}); idx=0; PAIRS=()
for t in "${EXP[@]}"; do
  if [[ "$t" =~ ^([0-9]+):([A-Za-z0-9_-]+)$ ]]; then PR=${BASH_REMATCH[1]}; L=${BASH_REMATCH[2]}
  elif [[ "$t" =~ ^([0-9]+)$ ]]; then PR=${BASH_REMATCH[1]}; L="${alpha[$idx]}"; idx=$((idx+1))
  else echo "Bad token: $t"; exit 2; fi
  PAIRS+=("$PR:$L")
done

OUT="docs/runs/${GROUP}.md"; mkdir -p docs/runs
{
  echo "# ${GROUP} — Pass anthology (PR bodies)"
  echo
  echo "| Label | PR | Link |"; echo "|--:|--:|:--|"
  for p in "${PAIRS[@]}"; do IFS=: read -r pr lbl <<<"$p"
    url=$(gh pr view "$pr" --json url -q .url); echo "| $lbl | #$pr | $url |"
  done
  for p in "${PAIRS[@]}"; do IFS=: read -r pr lbl <<<"$p"
    title=$(gh pr view "$pr" --json title -q .title)
    body=$(gh pr view "$pr" --json body -q .body)
    echo; echo "## Run $lbl — PR #$pr — $title"; echo
    [[ -n "$body" ]] && echo "$body" || echo "_(empty body)_"
  done
} > "$OUT"
echo "[pass-bodies] wrote $OUT"
