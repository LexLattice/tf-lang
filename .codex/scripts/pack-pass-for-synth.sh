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

if ! REPO_FULL=$(gh repo view --json nameWithOwner -q .nameWithOwner 2>/dev/null); then
  echo "Unable to determine repository (gh repo view failed)" >&2
  exit 1
fi
REPO_OWNER="${REPO_FULL%%/*}"
REPO_NAME="${REPO_FULL#*/}"

REVIEW_THREAD_QUERY=$(cat <<'GRAPHQL'
query($owner: String!, $name: String!, $number: Int!, $cursor: String) {
  repository(owner: $owner, name: $name) {
    pullRequest(number: $number) {
      reviewThreads(first: 50, after: $cursor) {
        nodes {
          isResolved
          path
          comments(first: 100) {
            nodes {
              author { login }
              body
              path
              line
              originalLine
            }
          }
        }
        pageInfo {
          hasNextPage
          endCursor
        }
      }
    }
  }
}
GRAPHQL
)

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
    if [[ -n "$body" ]]; then
      printf '%s\n' "$body"
    else
      echo "_(empty body)_"
    fi
  } >> "$OUT_MD"

  # Reviews, review comments, and review threads (GraphQL) for Markdown/JSON filtering
  base=$(gh pr view "$pr" --json reviews,comments)
  threads_json='[]'
  cursor=""
  while :; do
    if [[ -n "$cursor" ]]; then
      if ! resp=$(gh api graphql \
          -f query="$REVIEW_THREAD_QUERY" \
          -F owner="$REPO_OWNER" -F name="$REPO_NAME" \
          -F number="$pr" -F cursor="$cursor" 2>/dev/null); then
        threads_json='[]'
        break
      fi
    else
      if ! resp=$(gh api graphql \
          -f query="$REVIEW_THREAD_QUERY" \
          -F owner="$REPO_OWNER" -F name="$REPO_NAME" \
          -F number="$pr" 2>/dev/null); then
        threads_json='[]'
        break
      fi
    fi

    nodes=$(jq -c '.data.repository.pullRequest.reviewThreads.nodes // [] | map(.comments = (.comments.nodes // []))' <<<"$resp")
    [[ -n "$nodes" ]] || nodes='[]'
    threads_json=$(jq -c --argjson nodes "$nodes" '. + $nodes' <<<"$threads_json")

    has_next=$(jq -r '.data.repository.pullRequest.reviewThreads.pageInfo.hasNextPage' <<<"$resp")
    if [[ "$has_next" != "true" ]]; then
      break
    fi
    cursor=$(jq -r '.data.repository.pullRequest.reviewThreads.pageInfo.endCursor // empty' <<<"$resp")
    [[ -n "$cursor" ]] || break
  done

  raw=$(jq -c --argjson threads "$threads_json" '. + {reviewThreads: $threads}' <<<"$base")
  allow_json=$(printf '%s\n' "${ALLOW[@]}" | jq -R . | jq -s .)
  filt=$(jq -c --argjson allow "$allow_json" '
      def keep_allowed($allow):
        (. // []
          | map(select((.author.login? // "") as $u | ($allow | index($u)) != null and ($u | length) > 0)));
      .reviews  = ((.reviews  // []) | keep_allowed($allow))
      | .comments = ((.comments // []) | keep_allowed($allow))
      | .reviewThreads = ((.reviewThreads // [])
          | map(.comments = ((.comments // []) | keep_allowed($allow)))
          | map(select((.comments | length) > 0)))
    ' <<<"$raw")

  echo -e "\n### Selected Reviews (codex/gemini)\n" >> "$OUT_MD"
  reviews_md=$(jq -r '.reviews[]? | "- **\(.author.login)** (\(.state)): \((.body // "") | gsub("\r";""))"' <<<"$filt")
  comments_md=$(jq -r '.comments[]? | "- **\(.author.login)**: \((.body // "") | gsub("\r";""))"' <<<"$filt")
  if [[ -n "$reviews_md" || -n "$comments_md" ]]; then
    [[ -n "$reviews_md" ]] && printf '%s\n' "$reviews_md" >> "$OUT_MD"
    [[ -n "$comments_md" ]] && printf '%s\n' "$comments_md" >> "$OUT_MD"
  else
    echo "_No selected reviews or comments._" >> "$OUT_MD"
  fi

  echo -e "\n### Selected Review Threads (codex/gemini)\n" >> "$OUT_MD"
  threads_md=$(jq -r '
    (.reviewThreads // [])[]? as $thread
    | ($thread.comments | if length > 0 then .[0] else {} end) as $first
    | "- **Thread** on `\($thread.path // ($first.path // "(no path)"))`" +
        (if ($first.line // $first.originalLine) != null then
           " (line " + (($first.line // $first.originalLine) | tostring) + ")"
         else ""
         end) +
        " (" + (if $thread.isResolved then "resolved" else "open" end) + ")" ,
      ($thread.comments[]? | "  - **\(.author.login)**: \((.body // "") | gsub("\r";""))")
  ' <<<"$filt")
  if [[ -n "$threads_md" ]]; then
    printf '%s\n' "$threads_md" >> "$OUT_MD"
  else
    echo "_No selected review threads._" >> "$OUT_MD"
  fi

  # JSON row includes filtered reviews/comments; optionally add diff
  if [[ $INCLUDE_DIFF -eq 1 ]]; then
    diff_txt="$(gh pr diff "$pr" 2>/dev/null || true)"
    row=$(jq -c --arg lbl "$lbl" --arg pr "$pr" --arg url "$url" --arg title "$title" \
                --arg state "$state" --arg body "$body" --argjson rc "$filt" \
                --arg diff "$diff_txt" '
          {label:$lbl, pr:($pr|tonumber), url:$url, title:$title, state:$state, body:$body,
           reviews: ($rc.reviews // []), comments: ($rc.comments // []),
           reviewThreads: ($rc.reviewThreads // []), diff: $diff}
        ' <<<"{}")
  else
    row=$(jq -c --arg lbl "$lbl" --arg pr "$pr" --arg url "$url" --arg title "$title" \
                --arg state "$state" --arg body "$body" --argjson rc "$filt" '
          {label:$lbl, pr:($pr|tonumber), url:$url, title:$title, state:$state, body:$body,
           reviews: ($rc.reviews // []), comments: ($rc.comments // []),
           reviewThreads: ($rc.reviewThreads // [])}
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
    diff_txt="$(git show "$COMMIT_SHA" 2>/dev/null || echo)"
    commit_section=$(jq -nc --arg sha "$COMMIT_SHA" --arg diff "$diff_txt" '{sha:$sha, diffText:$diff}')
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
