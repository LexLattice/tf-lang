#!/usr/bin/env bash
# Bundle GitHub PRs (range or list) into one markdown file.
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  prbundle.sh [-r owner/repo] [-o out.md] PRS...
  PRS tokens can be numbers or ranges: "19-22 30 34-33"

Default output:
  docs/pr/pr<PRS>.md  (e.g., PRS="19-22" -> docs/pr/pr19_22.md)

Examples:
  ./scripts/prbundle.sh 19-22
  ./scripts/prbundle.sh -r LexLattice/tf-lang 19 20 21 22
  OUT=docs/pr/custom.md ./scripts/prbundle.sh 30-35

Test note:
  Set SKIP_GH=1 to skip GitHub API calls (for offline tests).
EOF
}

# Defaults (can be overridden via flags or env)
REPO="${REPO:-LexLattice/tf-lang}"
# OUT default computed from PR tokens if not provided
OUT="${OUT:-}"

# Flags
while getopts ":r:o:h" opt; do
  case "$opt" in
    r) REPO="$OPTARG" ;;
    o) OUT="$OPTARG" ;;
    h) usage; exit 0 ;;
    \?) echo "Unknown option: -$OPTARG" >&2; usage; exit 2 ;;
    :)  echo "Missing arg for -$OPTARG" >&2; usage; exit 2 ;;
  esac
done
shift $((OPTIND-1))

[ $# -gt 0 ] || { echo "ERROR: provide PR numbers or ranges"; usage; exit 2; }

# Optional: allow offline test mode without gh
SKIP_GH="${SKIP_GH:-0}"
if [[ "$SKIP_GH" != "1" ]]; then
  command -v gh >/dev/null 2>&1 || { echo "ERROR: 'gh' not found. Install https://cli.github.com/"; exit 1; }
fi

name_from_tokens() {
  local -a toks parts=()
  IFS=", " read -r -a toks <<< "$*"
  for t in "${toks[@]}"; do
    [[ -z "$t" ]] && continue
    if [[ "$t" =~ ^([0-9]+)-([0-9]+)$ ]]; then
      parts+=("${BASH_REMATCH[1]}_${BASH_REMATCH[2]}")
    elif [[ "$t" =~ ^[0-9]+$ ]]; then
      parts+=("$t")
    fi
  done
  if ((${#parts[@]} > 0)); then
    local IFS=_
    echo "pr${parts[*]}"
  else
    echo "prbundle"
  fi
}

expand_prs() {
  local -a toks out=()
  IFS=", " read -r -a toks <<< "$*"
  for t in "${toks[@]}"; do
    [[ -z "$t" ]] && continue
    if [[ "$t" =~ ^([0-9]+)-([0-9]+)$ ]]; then
      local s="${BASH_REMATCH[1]}" e="${BASH_REMATCH[2]}"
      if (( s <= e )); then seq "$s" "$e"; else seq "$s" -1 "$e"; fi
    elif [[ "$t" =~ ^[0-9]+$ ]]; then
      echo "$t"
    else
      echo "WARN: skipping invalid token '$t'" >&2
    fi
  done
}

NAME="$(name_from_tokens "$*")"
mapfile -t PRS < <(expand_prs "$*")
[ "${#PRS[@]}" -gt 0 ] || { echo "No valid PRs parsed."; exit 3; }

if [[ -z "$OUT" ]]; then
  OUT="docs/pr/${NAME}.md"
fi
mkdir -p "$(dirname "$OUT")"

: > "$OUT"
{
  echo "# PR Bundle for $REPO"
  printf -- "- Generated: %(%Y-%m-%d %H:%M:%S UTC)T\n" -1
  echo "- PRs: ${PRS[*]}"
  echo
  echo "## Summary"
  echo
} >> "$OUT"

# Summary bullets
for i in "${PRS[@]}"; do
  if [[ "$SKIP_GH" == "1" ]]; then
    echo "- **#${i}**" >> "$OUT"
  else
    title=$(gh pr view "$i" --repo "$REPO" --json title -q .title 2>/dev/null || echo "(unknown)")
    url=$(gh pr view "$i" --repo "$REPO" --json url -q .url 2>/dev/null || echo "")
    author=$(gh pr view "$i" --repo "$REPO" --json author -q .author.login 2>/dev/null || echo "")
    checks=$(gh pr checks "$i" --repo "$REPO" 2>/dev/null | awk '/^✓|^X|^×|^✗/{pass=1} END{print (pass?"has":"none")}' || echo "n/a")
    echo "- **#${i}** — ${title} ${url:+([link](${url}))} ${author:+— by @${author}} — checks: ${checks}" >> "$OUT"
  fi
done

# Full sections
for i in "${PRS[@]}"; do
  echo -e "\n\n---\n" >> "$OUT"
  if [[ "$SKIP_GH" == "1" ]]; then
    {
      echo "# PR #$i"
      echo "(offline mode; metadata omitted)"
    } >> "$OUT"
  else
    title=$(gh pr view "$i" --repo "$REPO" --json title -q .title 2>/dev/null || echo "(unknown)")
    url=$(gh pr view "$i" --repo "$REPO" --json url -q .url 2>/dev/null || echo "")
    author=$(gh pr view "$i" --repo "$REPO" --json author -q .author.login 2>/dev/null || echo "")
    created=$(gh pr view "$i" --repo "$REPO" --json createdAt -q .createdAt 2>/dev/null || echo "")
    updated=$(gh pr view "$i" --repo "$REPO" --json updatedAt -q .updatedAt 2>/dev/null || echo "")

    {
      echo "# PR #$i — $title"
      echo "- URL: $url"
      echo "- Author: ${author:+@}$author"
      echo "- Created: $created"
      echo "- Updated: $updated"
      echo
      echo "## Checks"
      echo '```'
      gh pr checks "$i" --repo "$REPO" || true
      echo '```'
      echo
      echo "## Comments"
      echo '```md'
      gh pr view "$i" --repo "$REPO" --comments || true
      echo '```'
      echo
      echo "## Files Changed (JSON)"
      echo '```json'
      gh api "repos/$REPO/pulls/$i/files" || true
      echo '```'
      echo
      echo "## Diff"
      echo '```diff'
      gh pr diff "$i" --repo "$REPO" || true
      echo '```'
      echo
      echo "## Meta (JSON)"
      echo '```json'
      gh pr view "$i" --repo "$REPO" \
        --json number,title,author,mergeStateStatus,reviewDecision,isDraft,createdAt,updatedAt,reviews,url,statusCheckRollup || true
      echo '```'
    } >> "$OUT"
  fi
done

echo "Wrote $OUT"
