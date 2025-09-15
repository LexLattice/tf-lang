#!/usr/bin/env bash
set -euo pipefail

# Usage:
#   pack-pass-for-synth.sh [-all] <GROUP> <PR|PR-PR|PR[:LABEL]>...
# Example:
#   pack-pass-for-synth.sh -all T1_1_P1 92-96
#   pack-pass-for-synth.sh T1_1_P1 92:A 93:B 94:C 95:D 96:E

INCLUDE_DIFF=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    -all|--all) INCLUDE_DIFF=1; shift ;;
    --) shift; break ;;
    -*) echo "Unknown flag: $1" >&2; exit 2 ;;
    *) break ;;
  esac
done

[[ $# -ge 2 ]] || { echo "Usage: $0 [-all] <GROUP> <PR|PR-PR|PR[:LABEL]>..."; exit 2; }
command -v gh >/dev/null || { echo "Requires GitHub CLI: gh"; exit 1; }
command -v jq >/dev/null || { echo "Requires jq"; exit 1; }

GROUP="$1"; shift

# Expand ranges and normalize tokens
TOK=("$@"); EXP=()
for t in "${TOK[@]}"; do
  if [[ "$t" =~ ^([0-9]+)-([0-9]+)$ ]]; then
    s=${BASH_REMATCH[1]}; e=${BASH_REMATCH[2]}
    (( e < s )) && { tmp=$s; s=$e; e=$tmp; }
    for ((i=s;i<=e;i++)); do EXP+=("$i"); done
  else
    EXP+=("$t")
  fi
done

# Auto-label with A, B, C... when label not provided
alpha=({A..Z}); idx=0; PAIRS=()
for t in "${EXP[@]}"; do
  if [[ "$t" =~ ^([0-9]+):([A-Za-z0-9_-]+)$ ]]; then
    PAIRS+=("$t")
  elif [[ "$t" =~ ^([0-9]+)$ ]]; then
    PAIRS+=("${t}:${alpha[$idx]}" ); idx=$((idx+1))
  else
    echo "Bad token: $t" >&2; exit 2
  fi
done

OUT_DIR="docs/runs"; mkdir -p "$OUT_DIR"
OUT_MD="${OUT_DIR}/${GROUP}_input.md"
OUT_JSON="${OUT_DIR}/${GROUP}.json"

# Header
{
  echo "# ${GROUP} — Synthesis Input"
  echo
  echo "| Label | PR | Link | State |"
  echo "|--:|--:|:--|:-----|"
} > "$OUT_MD"

printf '{ "group": "%s", "runs": [' "$GROUP" > "$OUT_JSON"; first=1

# Store allow-listed reviews/comments into JSON; show only those in Markdown
ALLOW=('chatgpt-codex-connector' 'gemini-code-assist')

for pl in "${PAIRS[@]}"; do
  pr="${pl%%:*}"; lbl="${pl#*:}"

  # Core PR metadata
  url=$(gh pr view "$pr" --json url -q .url)
  state=$(gh pr view "$pr" --json state,mergedAt -q 'if .mergedAt then "merged" else .state end')
  title=$(gh pr view "$pr" --json title -q .title)
  body=$(gh pr view "$pr" --json body -q .body)

  echo "| $lbl | #$pr | $url | $state |" >> "$OUT_MD"
  {
    echo
    echo "---"
    echo
    echo "## Run $lbl — PR #$pr — $title"
    echo
    echo "### PR Body"
    echo
    [[ -n "$body" ]] && echo "$body" || echo "_(empty body)_"
  } >> "$OUT_MD"

  # Reviews and issue comments; filter to allowed bot users for Markdown
  raw=$(gh pr view "$pr" --json reviews,comments)
  allow_json=$(printf '%s\n' "${ALLOW[@]}" | jq -R . | jq -s .)
  filt=$(jq -c --argjson allow "$allow_json" '
      .reviews  = (.reviews  // [] | map(select(.author.login as $u | $allow | index($u))))
      | .comments = (.comments // [] | map(select(.author.login as $u | $allow | index($u))))
    ' <<<"$raw")

  echo -e "\n### Selected Reviews (codex/gemini)\n" >> "$OUT_MD"
  jq -r '.reviews[]? | "- **\(.author.login)** (\(.state)): \((.body // "") | gsub("\r";""))"' <<<"$filt" >> "$OUT_MD"
  jq -r '.comments[]? | "- **\(.author.login)**: \((.body // "") | gsub("\r";""))"' <<<"$filt" >> "$OUT_MD"

  # JSON row includes filtered reviews/comments; optionally add diff
  if [[ $INCLUDE_DIFF -eq 1 ]]; then
    diff_txt="$(gh pr diff "$pr" 2>/dev/null || true)"
    row=$(jq -c --arg lbl "$lbl" --arg pr "$pr" --arg url "$url" --arg title "$title" \
                --arg state "$state" --arg body "$body" --argjson rc "$filt" \
                --arg diff "$diff_txt" '
          {label:$lbl, pr:($pr|tonumber), url:$url, title:$title, state:$state, body:$body,
           reviews: ($rc.reviews // []), comments: ($rc.comments // []), diff: $diff}
        ' <<<"{}")
  else
    row=$(jq -c --arg lbl "$lbl" --arg pr "$pr" --arg url "$url" --arg title "$title" \
                --arg state "$state" --arg body "$body" --argjson rc "$filt" '
          {label:$lbl, pr:($pr|tonumber), url:$url, title:$title, state:$state, body:$body,
           reviews: ($rc.reviews // []), comments: ($rc.comments // [])}
        ' <<<"{}")
  fi
  if [[ $first -eq 0 ]]; then printf ',' >> "$OUT_JSON"; fi
  printf '\n%s' "$row" >> "$OUT_JSON"; first=0
done

printf '\n]}\n' >> "$OUT_JSON"
echo "[pack] wrote:"
echo " - $OUT_MD"
echo " - $OUT_JSON"
