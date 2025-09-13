#!/usr/bin/env bash
# Purge stale PR remote-tracking refs and sanitize repo-local git config.
# - Removes remote "codex" if present
# - Deletes refs/remotes/codex/* and refs/remotes/origin/{pr,merge}/*
# - Removes PR refspecs from remote.origin.fetch
# - Prunes origin and tags
#
# Usage:
#   ./.codex/scripts/git-clean-refs.sh [--sanitize-config-only]
#   ./.codex/scripts/git-clean-refs.sh --sanitize-config   # alias
#
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || echo "")"
if [[ -z "$ROOT" ]]; then
  echo "Not inside a git repo." >&2
  exit 1
fi
cd "$ROOT"

SANITIZE_ONLY=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --sanitize-config|--sanitize-config-only) SANITIZE_ONLY=1; shift ;;
    -h|--help)
      sed -n '1,60p' "$0"; exit 0 ;;
    *) echo "Unknown arg: $1" >&2; exit 2 ;;
  esac
done

removed_remote=0
deleted_refs=()
deleted_count=0
unset_refspecs=()
unset_count=0

has_remote() { git remote | grep -qx "$1"; }

delete_ref_glob() {
  local glob="$1"
  # Use for-each-ref to handle packed-refs as well
  while IFS= read -r ref; do
    [[ -z "$ref" ]] && continue
    git update-ref -d "$ref" || true
    deleted_refs+=("$ref"); deleted_count=$((deleted_count+1))
  done < <(git for-each-ref --format='%(refname)' "$glob" || true)
}

sanitize_origin_refspecs() {
  # Remove any origin fetch refspecs matching GitHub PR patterns
  # e.g., +refs/pull/*/head:refs/remotes/origin/pr/*
  #       +refs/pull/*/merge:refs/remotes/origin/merge/*
  mapfile -t vals < <(git config --get-all remote.origin.fetch 2>/dev/null || true)
  for v in "${vals[@]:-}"; do
    [[ -z "$v" ]] && continue
    if [[ "$v" == *"refs/pull/"* || "$v" == *"refs/merge/"* || "$v" == *"/pr/"* || "$v" == *"/merge/"* ]]; then
      git config --unset-all remote.origin.fetch "$v" || true
      unset_refspecs+=("$v"); unset_count=$((unset_count+1))
    fi
  done
}

if (( SANITIZE_ONLY )); then
  sanitize_origin_refspecs
else
  # Remove remote 'codex' if present (do not touch origin/upstream)
  if has_remote codex; then
    git remote remove codex || true
    removed_remote=1
  fi

  # Delete remote-tracking refs under codex/* and origin/pr/*, origin/merge/*
  delete_ref_glob 'refs/remotes/codex/*'
  delete_ref_glob 'refs/remotes/origin/pr/*'
  delete_ref_glob 'refs/remotes/origin/merge/*'

  # Sanitize origin fetch refspecs (remove PR/merge patterns)
  sanitize_origin_refspecs

  # Prune origin and tags to clean up any stale tracking refs
  git fetch origin --prune --prune-tags >/dev/null 2>&1 || true
  git remote prune origin >/dev/null 2>&1 || true
fi

# Summary output
echo "[git-clean-refs] repo: $ROOT"
if (( removed_remote )); then
  echo "- removed remote: codex"
else
  echo "- remote 'codex' not present"
fi
echo "- deleted refs: $deleted_count"
if (( deleted_count > 0 )); then
  printf '  - %s\n' "${deleted_refs[@]}"
fi
echo "- removed origin fetch refspecs: $unset_count"
if (( unset_count > 0 )); then
  printf '  - %s\n' "${unset_refspecs[@]}"
fi
echo "- pruned: origin (tags/prune)"

exit 0

