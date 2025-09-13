#!/usr/bin/env bash
set -euo pipefail

# Usage: ./.codex/scripts/hot-update.sh <RUN_ID e.g., D1_2> <PR_RANGE e.g., 70-73> [-r owner/repo] [--remote origin] [--commit -m "..."]
RUN_ID="${1:-}"; shift || true
PR_RANGE="${1:-}"; shift || true

if [[ -z "$RUN_ID" || -z "$PR_RANGE" ]]; then
  echo "Usage: $0 <RUN_ID> <PR_RANGE> [extra flags...]" >&2
  exit 2
fi

REPO=""
REMOTE="origin"
DO_COMMIT=0
COMMIT_MSG="codex: hot review ($RUN_ID $PR_RANGE)"

while [[ $# -gt 0 ]]; do
  case "$1" in
    -r) REPO="$2"; shift 2 ;;
    --remote) REMOTE="$2"; shift 2 ;;
    --commit) DO_COMMIT=1; shift ;;
    -m|--message) COMMIT_MSG="$2"; shift 2 ;;
    *) echo "Unknown arg: $1" >&2; exit 2 ;;
  esac
done

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

# Expand "70-73" → 70 71 72 73
expand_range() {
  local tok="$1"
  if [[ "$tok" =~ ^([0-9]+)-([0-9]+)$ ]]; then
    local s="${BASH_REMATCH[1]}" e="${BASH_REMATCH[2]}"
    if (( s <= e )); then seq "$s" "$e"; else seq "$s" -1 "$e"; fi
  else
    echo "$tok"
  fi
}
mapfile -t PRS < <(expand_range "$PR_RANGE")

# A/B/C/D labels in numeric order
LABELS=(A B C D)
PRS_SPEC=()
for i in "${!PRS[@]}"; do
  PRS_SPEC+=("${PRS[$i]}:${LABELS[$i]}")
done

REVIEWS_DIR=".codex/reviews"
mkdir -p "$REVIEWS_DIR"

RUNS_OUT="${REVIEWS_DIR}/${RUN_ID} agent runs ${PR_RANGE}.md"
BUNDLE_OUT="${REVIEWS_DIR}/${RUN_ID} pr bundle ${PR_RANGE}.md"

# 1) Collect per-agent artifacts to .codex/runs/<RUN_ID>/..., and write the consolidated anthology to reviews:
./collect-run-reports.sh \
  --runs-root ".codex/runs" \
  --run-id "$RUN_ID" \
  --remote "$REMOTE" \
  --winner-out "$RUNS_OUT" \
  --prs "${PRS_SPEC[@]}"

# 2) Generate PR bundle into reviews with your filename:
if [[ -n "$REPO" ]]; then
  ./prbundle.sh -r "$REPO" -o "$BUNDLE_OUT" "${PRS[@]}"
else
  if command -v gh >/dev/null 2>&1; then
    REPO_DET="$(gh repo view --json nameWithOwner -q .nameWithOwner 2>/dev/null || true)"
    if [[ -n "$REPO_DET" ]]; then
      ./prbundle.sh -r "$REPO_DET" -o "$BUNDLE_OUT" "${PRS[@]}"
    else
      ./prbundle.sh -o "$BUNDLE_OUT" "${PRS[@]}"
    fi
  else
    ./prbundle.sh -o "$BUNDLE_OUT" "${PRS[@]}"
  fi
fi

# 3) Optionally commit:
if (( DO_COMMIT )); then
  git add ".codex/runs/${RUN_ID}" "$RUNS_OUT" "$BUNDLE_OUT"
  git commit -m "$COMMIT_MSG"
  echo "Committed: $COMMIT_MSG"
else
  echo "Reviews ready:"
  echo "  $RUNS_OUT"
  echo "  $BUNDLE_OUT"
fi
