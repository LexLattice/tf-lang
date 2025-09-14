#!/usr/bin/env bash
# Run only tests relevant to changed paths for the push range.
# Falls back to all tests if range can't be determined.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

# Allow forcing the slow/full path
if [[ "${FAST_PATH_DISABLE:-0}" == "1" ]]; then
  echo "[changed] FAST_PATH_DISABLE=1 -> running full test suite"
  exec ./.codex/scripts/test-all.sh
fi

# Pre-push passes refs on stdin as: <local_ref> <local_sha> <remote_ref> <remote_sha>
local_shas=()
remote_shas=()
while read -r lref lsha rref rsha; do
  local_shas+=("$lsha")
  remote_shas+=("$rsha")
done

# Collect changed files across all refs
FILES=()
if [[ ${#local_shas[@]} -gt 0 ]]; then
  for i in "${!local_shas[@]}"; do
    lsha="${local_shas[$i]}"
    rsha="${remote_shas[$i]}"
    if [[ -z "$rsha" || "$rsha" =~ ^0+$ ]]; then
      if git rev-parse --verify --quiet "${lsha}^"; then
        mapfile -t diff_files < <(git diff --name-only "${lsha}^" "${lsha}")
      else
        mapfile -t diff_files < <(git show --name-only --pretty='' "${lsha}")
      fi
    else
      mapfile -t diff_files < <(git diff --name-only "${rsha}..${lsha}")
    fi
    FILES+=("${diff_files[@]}")
  done
  mapfile -t FILES < <(printf '%s\n' "${FILES[@]}" | sort -u)
else
  # Fallback: compare working HEAD against merge-base with origin/main (best effort)
  base="$(git merge-base HEAD origin/main 2>/dev/null || true)"
  if [[ -n "${base}" ]]; then
    mapfile -t FILES < <(git diff --name-only "${base}..HEAD")
  else
    mapfile -t FILES < <(git show --name-only --pretty='' HEAD)
  fi
fi

if [[ ${#FILES[@]} -eq 0 ]]; then
  echo "[changed] No files detected in range; running full suite for safety."
  exec ./.codex/scripts/test-all.sh
fi

echo "[changed] Detected ${#FILES[@]} changed files"

NEED_TS=0
NEED_RUST=0
NEED_GOLDEN=0
ONLY_DOCS=1

for f in "${FILES[@]}"; do
  case "$f" in
    packages/tf-lang-l0-ts/*) NEED_TS=1; ONLY_DOCS=0 ;;
    packages/tf-lang-l0-rs/*) NEED_RUST=1; ONLY_DOCS=0 ;;
    packages/adapter-legal-ts/*|packages/claims-core-ts/*) NEED_GOLDEN=1; ONLY_DOCS=0 ;;
    docs/data/*) NEED_GOLDEN=1; ONLY_DOCS=0 ;;  # dataset changes require golden
    .golden/*) NEED_GOLDEN=1; ONLY_DOCS=0 ;;
    *.md|docs/*) : ;;  # ignore docs
    .github/*|scripts/*|Makefile|package.json|pnpm-workspace.yaml) ONLY_DOCS=0 ;;
    *) ONLY_DOCS=0 ;;
  esac
done

# If nothing requires tests, decide whether to skip or run full suite
if [[ $NEED_TS -eq 0 && $NEED_RUST -eq 0 && $NEED_GOLDEN -eq 0 ]]; then
  if [[ $ONLY_DOCS -eq 1 ]]; then
    echo "[changed] Only documentation changes detected; skipping tests."
    exit 0
  fi
  echo "[changed] No targeted packages flagged; running full suite for safety."
  exec ./.codex/scripts/test-all.sh
fi

# Run as needed
if [[ $NEED_TS -eq 1 ]]; then
  echo "[changed] Running TypeScript tests (tf-lang-l0-ts)"
  pnpm -C packages/tf-lang-l0-ts test
fi

if [[ $NEED_RUST -eq 1 ]]; then
  echo "[changed] Running Rust tests (tf-lang-l0-rs)"
  cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml
fi

if [[ $NEED_GOLDEN -eq 1 ]]; then
  echo "[changed] Running golden check (claims/extractor/precedence touched)"
  ./.codex/scripts/golden.sh
fi

echo "[changed] Done."
