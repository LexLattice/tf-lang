#!/usr/bin/env bash
# Aggregate parallel-run reports into the current (winner) branch.
# Usage examples:
#   ./.codex/scripts/collect-run-reports.sh --prs 30:A 31:B 32:C 33:D
#   ./.codex/scripts/collect-run-reports.sh --commit -m "collect reports" --prs 30:A 31:B 32:C 33:D
#
# Requirements: git; optional: gh (GitHub CLI) for nicer titles (falls back gracefully).

set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

RUNS_ROOT=".codex/runs"
RUN_ID=""
REMOTE="origin"
WINNER_OUT=""
RUNS_DIR="$RUNS_ROOT"

FILES=("REPORT.md" "COMPLIANCE.md" "OBS_LOG.md" "CHANGES.md")
PRS_SPEC=()
DO_COMMIT=0
COMMIT_MSG="codex: collect parallel run reports"

# --- args ---
while [[ $# -gt 0 ]]; do
  case "$1" in
    --prs) shift; while [[ $# -gt 0 && "$1" != --* ]]; do PRS_SPEC+=("$1"); shift; done ;;
    --commit) DO_COMMIT=1; shift ;;
    -m|--message) COMMIT_MSG="$2"; shift 2 ;;
    --run-id) RUN_ID="$2"; shift 2 ;;
    --runs-root) RUNS_ROOT="$2"; shift 2 ;;
    --winner-out) WINNER_OUT="$2"; shift 2 ;;
    --remote) REMOTE="$2"; shift 2 ;;
    -h|--help) sed -n '1,60p' "$0"; exit 0 ;;
    *) echo "Unknown arg: $1" >&2; exit 1 ;;
  esac
done

if [[ ${#PRS_SPEC[@]} -eq 0 ]]; then
  echo "Use: --prs <pr[:LABEL]> ..." >&2; exit 1
fi

# Expand range tokens like "70-73" into 70 71 72 73
expand_tokens() {
  local t
  for t in "$@"; do
    if [[ "$t" =~ ^([0-9]+)-([0-9]+)$ ]]; then
      local s="${BASH_REMATCH[1]}" e="${BASH_REMATCH[2]}"
      if (( s <= e )); then seq "$s" "$e"; else seq "$s" -1 "$e"; fi
    else
      echo "$t"
    fi
  done
}

# Normalize: expand ranges, then sort and auto-label
mapfile -t PRS_SPEC < <(expand_tokens "${PRS_SPEC[@]}")

# Auto-label any entries missing :LABEL → A,B,C,...
LABELS=(A B C D E F G H I J K L)
# Sort PRs numerically for stable assignment (by PR number before optional colon)
mapfile -t PRS_SPEC < <(printf "%s\n" "${PRS_SPEC[@]}" | sort -n -t: -k1,1)
auto_i=0
for i in "${!PRS_SPEC[@]}"; do
  if [[ "${PRS_SPEC[$i]}" != *:* ]]; then
    PRS_SPEC[$i]="${PRS_SPEC[$i]}:${LABELS[$auto_i]}"
    auto_i=$((auto_i+1))
  fi
done

have_gh() { command -v gh >/dev/null 2>&1; }

append_section() {
  local run_label="$1" pr_num="$2" object_ref="$3" sha="$4" title="$5"
  local anthology="$ANTHOLOGY_FILE"

  {
    echo -e "\n---\n"
    echo "## Run ${run_label} — PR #${pr_num} (${sha:0:7})"
    [[ -n "$title" ]] && echo "_${title}_"
    for f in "${FILES[@]}"; do
      echo -e "\n### ${f}"
      if git cat-file -e "${object_ref}:${f}" 2>/dev/null; then
        echo -e '```md'
        git show "${object_ref}:${f}"
        echo -e '```'
      else
        echo "_(missing)_"
      fi
    done
  } >> "$anthology"
}

# Ensure we’re on a branch (winner PR branch)
CURRENT_BRANCH="$(git rev-parse --abbrev-ref HEAD)"
if [[ "$CURRENT_BRANCH" == "HEAD" ]]; then
  echo "You are in a detached HEAD. Checkout the winner branch first." >&2
  exit 1
fi

# Resolve output dirs/files
[[ -n "$RUN_ID" ]] && RUNS_DIR="${RUNS_ROOT}/${RUN_ID}"
mkdir -p "$RUNS_DIR"

ANTHOLOGY_FILE="${WINNER_OUT:-${RUNS_ROOT}/winner/RUNS_REPORTS.md}"
mkdir -p "$(dirname "$ANTHOLOGY_FILE")"
echo "# Parallel run aggregation" > "$ANTHOLOGY_FILE"
echo "_Winner branch: ${CURRENT_BRANCH} — $(date -u +"%Y-%m-%dT%H:%M:%SZ")_" >> "$ANTHOLOGY_FILE"

# Process each PR:LABEL
for spec in "${PRS_SPEC[@]}"; do
  IFS=":" read -r pr label <<<"$spec"
  label="${label:-X}"
  echo "Fetching PR #${pr} (ephemeral) ..."
  # Ephemeral fetch: FETCH_HEAD only; do not create local refs
  git fetch --no-tags -q "$REMOTE" "pull/${pr}/head" || {
    echo "Failed to fetch PR #${pr} (pull/${pr}/head). Ensure remote '$REMOTE' points to GitHub." >&2
    exit 1
  }

  sha="$(git rev-parse FETCH_HEAD)"
  title=""
  if have_gh; then
    title="$(gh pr view "$pr" --json title --jq .title 2>/dev/null || true)"
  fi

  # Materialize per-run folder and copy files (if present)
  RUN_DIR="$RUNS_DIR/${label}"
  mkdir -p "$RUN_DIR"
  for f in "${FILES[@]}"; do
    if git cat-file -e "${sha}:${f}" 2>/dev/null; then
      git show "${sha}:${f}" > "${RUN_DIR}/${f}"
    fi
  done

  # Append to anthology
  append_section "$label" "$pr" "$sha" "$sha" "$title"
done

# Stage artifacts (best-effort; ignore if gitignored)
git add "$RUNS_DIR" 2>/dev/null || true
git add "$ANTHOLOGY_FILE" 2>/dev/null || true

if [[ $DO_COMMIT -eq 1 ]]; then
  git commit -m "$COMMIT_MSG"
  echo "Committed aggregation: $COMMIT_MSG"
else
  echo "Aggregation complete. Review changes and commit when ready."
fi
