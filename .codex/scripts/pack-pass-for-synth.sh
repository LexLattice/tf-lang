#!/usr/bin/env bash
set -euo pipefail

# Usage:
#   pack-pass-for-synth.sh [-all] [--commit <sha>] <GROUP> [<PR|PR-PR|PR[:LABEL]>...]
# Example:
#   pack-pass-for-synth.sh -all T1_1_P1 92-96
#   pack-pass-for-synth.sh T1_1_P1 92:A 93:B 94:C 95:D 96:E

INCLUDE_DIFF=0
COMMIT_SHA=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    -all|--all) INCLUDE_DIFF=1; shift ;;
    --commit) COMMIT_SHA="${2:-}"; [[ -n "$COMMIT_SHA" ]] || { echo "--commit requires a SHA" >&2; exit 2; }; shift 2 ;;
    --) shift; break ;;
    -*) echo "Unknown flag: $1" >&2; exit 2 ;;
    *) break ;;
  esac
done

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 [-all] [--commit <sha>] <GROUP> [<PR|PR-PR|PR[:LABEL]>...]" >&2
  exit 2
fi
command -v gh >/dev/null || { echo "Requires GitHub CLI: gh"; exit 1; }
command -v jq >/dev/null || { echo "Requires jq"; exit 1; }

# Resolve repo name for REST endpoints (review comments)
REPO_NAME="$(gh repo view --json nameWithOwner -q .nameWithOwner 2>/dev/null || echo)"

# Limit per-file diffs; files with more than DIFF_LIMIT changed lines are excluded
DIFF_LIMIT="${DIFF_LIMIT:-500}"

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

# Store allow-listed bot comments; filter out generic intro messages
# - Keep only comments from: chatgpt-codex-connector, gemini-code-assist
# - Drop intro messages:
#   * Codex: bodies starting with "Codex Review: Here are some suggestions."
#   * Gemini: bodies containing "Summary of Changes"
ALLOW=('chatgpt-codex-connector' 'gemini-code-assist')

# Precompute normalized diff sets for similarity summary
TMP_DIFFDIR=$(mktemp -d 2>/dev/null || mktemp -d -t packpass)
trap 'rm -rf "$TMP_DIFFDIR"' EXIT

declare -a LABS PRNUMS FILES
for pl in "${PAIRS[@]}"; do
  pr="${pl%%:*}"; lbl="${pl#*:}";
  LABS+=("$lbl"); PRNUMS+=("$pr");
  # Build normalized change-line set: file|sign|content (trimmed, collapsed ws)
  setfile="${TMP_DIFFDIR}/${lbl}.set"
  FILES+=("$setfile")
  gh pr diff "$pr" 2>/dev/null | awk -v thr="$DIFF_LIMIT" '
    function flush(){ if (tokn>0 && chg<=thr) { for(i=1;i<=tokn;i++) print tok[i]; } tokn=0; chg=0; file="" }
    BEGIN{ file=""; tokn=0; chg=0 }
    /^diff --git /{ flush(); next }
    /^\+\+\+ [ab]\//{ file=substr($0,7); next }
    /^--- [ab]\//{ next }
    /^[+-]/{
      if ($0 ~ /^\+\+\+ / || $0 ~ /^--- /) next;
      sign=substr($0,1,1); content=substr($0,2);
      gsub(/\r/,"",content); gsub(/[ \t]+/," ",content); sub(/^\s+/,"",content); sub(/\s+$/,"",content);
      tok[++tokn]=file "|" sign "|" content; chg++;
      next
    }
    END{ flush() }
  ' | LC_ALL=C sort -u > "$setfile" || :
done

# Compute similarity metrics
union_count=0; all_common_count=0
pair_lines=()
if ((${#FILES[@]} > 0)); then
  union_count=$(cat "${FILES[@]}" 2>/dev/null | LC_ALL=C sort -u | wc -l | awk '{print $1}')
  # Intersect across all
  cp "${FILES[0]}" "$TMP_DIFFDIR/_accum.set" 2>/dev/null || :
  if ((${#FILES[@]} > 1)); then
    for ((i=1;i<${#FILES[@]};i++)); do
      comm -12 "$TMP_DIFFDIR/_accum.set" "${FILES[$i]}" > "$TMP_DIFFDIR/_next.set" || :
      mv "$TMP_DIFFDIR/_next.set" "$TMP_DIFFDIR/_accum.set"
    done
  fi
  all_common_count=$(wc -l < "$TMP_DIFFDIR/_accum.set" 2>/dev/null | awk '{print $1}')
fi

{
  echo
  echo "### Diff Similarity Summary"
  echo
  # Per-PR counts
  printf '%s' "- Per-PR changed lines: "
  for ((i=0;i<${#LABS[@]};i++)); do
    cnt=$(wc -l < "${FILES[$i]}" 2>/dev/null | awk '{print $1}')
    printf "%s:%s%s" "${LABS[$i]}" "${cnt:-0}" $([[ $i -lt $((${#LABS[@]}-1)) ]] && echo ", " || echo "")
  done
  echo
  # Common across all
  if (( union_count > 0 )); then
    pct=$(awk -v a="$all_common_count" -v u="$union_count" 'BEGIN{ if(u==0)print 0; else printf "%.1f", (a/u)*100 }')
    echo "- Common across all: ${all_common_count}/${union_count} (${pct}%)"
  else
    echo "- Common across all: n/a"
  fi
  # Pairwise Jaccard
  if ((${#FILES[@]} > 1)); then
    echo "- Pairwise Jaccard similarity (intersection/union):"
    for ((i=0;i<${#FILES[@]};i++)); do
      for ((j=i+1;j<${#FILES[@]};j++)); do
        inter=$(comm -12 "${FILES[$i]}" "${FILES[$j]}" | wc -l | awk '{print $1}')
        un=$(cat "${FILES[$i]}" "${FILES[$j]}" | LC_ALL=C sort -u | wc -l | awk '{print $1}')
        pct=$(awk -v a="$inter" -v u="$un" 'BEGIN{ if(u==0)print 0; else printf "%.1f", (a/u)*100 }')
        echo "  - ${LABS[$i]} ↔ ${LABS[$j]}: ${pct}% (${inter}/${un})"
      done
    done
  fi
} >> "$OUT_MD"

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

  # Reviews and issue comments via GraphQL; keep only allowed bots, drop generic intros
  raw=$(gh pr view "$pr" --json reviews,comments)
  allow_json=$(printf '%s\n' "${ALLOW[@]}" | jq -R . | jq -s .)
  filt_gc=$(jq -c --argjson allow "$allow_json" '
      def drop_intro:
        ((.author.login == "chatgpt-codex-connector" and ((.body // "") | test("(?i)^\\s*Codex Review: Here are some suggestions\\."))) or
         (.author.login == "gemini-code-assist" and ((.body // "") | test("(?i)Summary of Changes"))))
        | not;
      {
        reviews:  (.reviews  // [] | map(select(.author.login as $u | $allow | index($u)) | select(drop_intro))),
        comments: (.comments // [] | map(select(.author.login as $u | $allow | index($u)) | select(drop_intro)))
      }
    ' <<<"$raw")

  # Review comments (inline code comments) via REST; keep only allowed bots, drop intros
  rc_filt='[]'
  if [[ -n "$REPO_NAME" ]]; then
    # Slurp paginated arrays into a single array, then filter
    rc_raw=$(gh api "repos/${REPO_NAME}/pulls/${pr}/comments" --paginate 2>/dev/null | jq -s '[ .[] | .[] ]' 2>/dev/null || echo '[]')
    rc_filt=$(jq -c --argjson allow "$allow_json" '
      def drop_intro:
        ((.user.login == "chatgpt-codex-connector" and ((.body // "") | test("(?i)^\\s*Codex Review: Here are some suggestions\\."))) or
         (.user.login == "gemini-code-assist" and ((.body // "") | test("(?i)Summary of Changes"))))
        | not;
      [ .[]? | select(.user.login as $u | $allow | index($u)) | select(drop_intro) ]
    ' <<<"$rc_raw")
  fi

  echo -e "\n### AI Comments (issue)\n" >> "$OUT_MD"
  jq -r '.comments[]? | "- **@\(.author.login)**: \((.body // "") | gsub("\r";""))"' <<<"$filt_gc" >> "$OUT_MD"
  echo -e "\n### AI Review Comments (inline)\n" >> "$OUT_MD"
  jq -r '.[]? | "- **@\(.user.login)** (\(.path)#:\(.original_line // .line // .position // 0)): \((.body // "") | gsub("\r";""))"' <<<"$rc_filt" >> "$OUT_MD"

  # JSON row includes filtered reviews/comments; optionally add diff
  if [[ $INCLUDE_DIFF -eq 1 ]]; then
    tmpdiff=$(mktemp)
    gh pr diff "$pr" > "$tmpdiff" 2>/dev/null || true
    tmpf=$(mktemp)
    awk -v thr="$DIFF_LIMIT" '
      function emit(){ if (bufn>0 && chg<=thr) { for(i=1;i<=bufn;i++) print buf[i]; } bufn=0; chg=0 }
      BEGIN{ bufn=0; chg=0 }
      /^diff --git /{ emit(); bufn=0; chg=0; buf[++bufn]=$0; next }
      {
        if ($0 ~ /^[+-]/ && $0 !~ /^\+\+\+ / && $0 !~ /^--- /) chg++;
        buf[++bufn]=$0; next
      }
      END{ emit() }
    ' "$tmpdiff" > "$tmpf" || cp "$tmpdiff" "$tmpf"
    row=$(jq -c --arg lbl "$lbl" --arg pr "$pr" --arg url "$url" --arg title "$title" \
                --arg state "$state" --arg body "$body" --argjson gc "$filt_gc" --argjson rc "$rc_filt" \
                --rawfile diff "$tmpf" '
          {label:$lbl, pr:($pr|tonumber), url:$url, title:$title, state:$state, body:$body,
           reviews: ($gc.reviews // []), comments: ($gc.comments // []), reviewComments: ($rc // []), diff: $diff}
        ' <<<"{}")
    rm -f "$tmpdiff" "$tmpf"
  else
    row=$(jq -c --arg lbl "$lbl" --arg pr "$pr" --arg url "$url" --arg title "$title" \
                --arg state "$state" --arg body "$body" --argjson gc "$filt_gc" --argjson rc "$rc_filt" '
          {label:$lbl, pr:($pr|tonumber), url:$url, title:$title, state:$state, body:$body,
           reviews: ($gc.reviews // []), comments: ($gc.comments // []), reviewComments: ($rc // [])}
        ' <<<"{}")
  fi
  if [[ $first -eq 0 ]]; then printf ',' >> "$OUT_JSON"; fi
  printf '\n%s' "$row" >> "$OUT_JSON"; first=0
done

# Optional commit diff section
commit_section=""
if [[ -n "$COMMIT_SHA" ]]; then
  if command -v gh >/dev/null 2>&1; then
    REPO_NAME="$(gh repo view --json nameWithOwner -q .nameWithOwner 2>/dev/null || echo)"
    if [[ -n "$REPO_NAME" ]]; then
      commit_section=$(gh api "repos/${REPO_NAME}/commits/${COMMIT_SHA}" \
        -q '{sha: .sha, stats: .stats, files: [.files[] | {filename,status,additions,deletions,patch}]}' 2>/dev/null || echo '')
    fi
  fi
  if [[ -z "$commit_section" ]]; then
    tmpc=$(mktemp)
    git show "$COMMIT_SHA" > "$tmpc" 2>/dev/null || true
    tmpc2=$(mktemp)
    awk -v thr="$DIFF_LIMIT" '
      function emit(){ if (bufn>0 && chg<=thr) { for(i=1;i<=bufn;i++) print buf[i]; } bufn=0; chg=0 }
      BEGIN{ bufn=0; chg=0 }
      /^diff --git /{ emit(); bufn=0; chg=0; buf[++bufn]=$0; next }
      {
        if ($0 ~ /^[+-]/ && $0 !~ /^\+\+\+ / && $0 !~ /^--- /) chg++;
        buf[++bufn]=$0; next
      }
      END{ emit() }
    ' "$tmpc" > "$tmpc2" || cp "$tmpc" "$tmpc2"
    commit_section=$(jq -nc --arg sha "$COMMIT_SHA" --rawfile diff "$tmpc2" '{sha:$sha, diffText:$diff}')
    rm -f "$tmpc" "$tmpc2"
  fi
fi

if [[ -n "$commit_section" ]]; then
  printf '\n],\n  "commit": %s\n}\n' "$commit_section" >> "$OUT_JSON"
else
  printf '\n]}\n' >> "$OUT_JSON"
fi
echo "[pack] wrote:"
echo " - $OUT_MD"
echo " - $OUT_JSON"
