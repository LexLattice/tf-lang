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

OUT_DIR=".codex/runs"
WIN_DIR="$OUT_DIR/winner"
mkdir -p "$WIN_DIR"

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
    -h|--help)
      sed -n '1,40p' "$0"; exit 0 ;;
    *)
      echo "Unknown arg: $1" >&2; exit 1 ;;
  esac
done

if [[ ${#PRS_SPEC[@]} -eq 0 ]]; then
  echo "No PR specs provided. Use: --prs 30:A 31:B 32:C 33:D" >&2
  exit 1
fi

have_gh() { command -v gh >/dev/null 2>&1; }

append_section() {
  local run_label="$1" pr_num="$2" branch_ref="$3" sha="$4" title="$5"
  local anthology="$WIN_DIR/RUNS_REPORTS.md"

  {
    echo -e "\n---\n"
    echo "## Run ${run_label} — PR #${pr_num} (${sha:0:7})"
    [[ -n "$title" ]] && echo "_${title}_"
    for f in "${FILES[@]}"; do
      echo -e "\n### ${f}"
      if git cat-file -e "${branch_ref}:${f}" 2>/dev/null; then
        echo -e '```md'
        git show "${branch_ref}:${f}"
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

echo "# Parallel run aggregation" > "$WIN_DIR/RUNS_REPORTS.md"
echo "_Winner branch: ${CURRENT_BRANCH} — $(date -u +"%Y-%m-%dT%H:%M:%SZ")_" >> "$WIN_DIR/RUNS_REPORTS.md"

# Process each PR:LABEL
for spec in "${PRS_SPEC[@]}"; do
  IFS=":" read -r pr label <<<"$spec"
  label="${label:-X}"
  tmp_ref="codex/pr-${pr}"

  echo "Fetching PR #${pr} → ${tmp_ref} ..."
  # Fetch PR head into a local ref (works on GitHub remotes)
  git fetch origin "pull/${pr}/head:${tmp_ref}" -q || {
    echo "Failed to fetch PR #${pr} (pull/${pr}/head). Ensure 'origin' points to GitHub." >&2
    exit 1
  }

  sha="$(git rev-parse "${tmp_ref}")"
  title=""
  if have_gh; then
    title="$(gh pr view "$pr" --json title --jq .title 2>/dev/null || true)"
  fi

  # Materialize per-run folder and copy files (if present)
  RUN_DIR="$OUT_DIR/${label}"
  mkdir -p "$RUN_DIR"
  for f in "${FILES[@]}"; do
    if git cat-file -e "${tmp_ref}:${f}" 2>/dev/null; then
      git show "${tmp_ref}:${f}" > "${RUN_DIR}/${f}"
    fi
  done

  # Append to anthology
  append_section "$label" "$pr" "$tmp_ref" "$sha" "$title"
done

# Stage artifacts
git add "$OUT_DIR"

if [[ $DO_COMMIT -eq 1 ]]; then
  git commit -m "$COMMIT_MSG"
  echo "Committed aggregation: $COMMIT_MSG"
else
  echo "Aggregation complete. Review changes and commit when ready."
fi
