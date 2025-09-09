#!/usr/bin/env bash
# Run only tests relevant to changed paths for the push range.
# Falls back to all tests if range can't be determined.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

# Allow forcing the slow/full path
if [[ "${FAST_PATH_DISABLE:-0}" == "1" ]]; then
  echo "[changed] FAST_PATH_DISABLE=1 -> running full test suite"
  exec scripts/test-all.sh
fi

# Pre-push passes refs on stdin as: <local_ref> <local_sha> <remote_ref> <remote_sha>
local_sha=""
remote_sha=""
while read -r lref lsha rref rsha; do
  local_sha="$lsha"
  remote_sha="$rsha"
done

# Determine diff range
range=""
if [[ -n "${local_sha}" ]]; then
  if [[ -z "${remote_sha}" || "${remote_sha}" =~ ^0+$ ]]; then
    # New branch / no remote SHA: fallback to last 20 commits or single commit
    if git rev-parse HEAD~20 >/dev/null 2>&1; then
      range="$(git rev-parse HEAD~20)..${local_sha}"
    else
      range="${local_sha}^!"
    fi
  else
    range="${remote_sha}..${local_sha}"
  fi
fi

# Collect changed files
if [[ -n "${range}" ]]; then
  mapfile -t FILES < <(git diff --name-only ${range})
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
  exec scripts/test-all.sh
fi

echo "[changed] Detected ${#FILES[@]} changed files in range: ${range:-'(fallback)'}"

NEED_TS=0
NEED_RUST=0
NEED_GOLDEN=0

for f in "${FILES[@]}"; do
  case "$f" in
    packages/tf-lang-l0-ts/*) NEED_TS=1 ;;
    packages/tf-lang-l0-rs/*) NEED_RUST=1 ;;
    packages/adapter-legal-ts/*|packages/claims-core-ts/*) NEED_GOLDEN=1 ;;
    docs/data/*) NEED_GOLDEN=1 ;;  # if dataset changes, enforce golden
    .github/*|scripts/*|Makefile|package.json|pnpm-workspace.yaml) : ;;
    *) : ;;
  esac
done

# If neither TS nor Rust flagged but we touched core infra, be safe and run both
if [[ $NEED_TS -eq 0 && $NEED_RUST -eq 0 && $NEED_GOLDEN -eq 0 ]]; then
  echo "[changed] No targeted packages flagged; running full suite for safety."
  exec scripts/test-all.sh
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
  scripts/golden.sh
fi

echo "[changed] Done."
