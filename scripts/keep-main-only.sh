#!/usr/bin/env bash

set -euo pipefail

REMOTE=${REMOTE:-origin}
MAIN_BRANCH=${MAIN_BRANCH:-main}

if ! command -v git >/dev/null 2>&1; then
  echo "Error: git not found in PATH" >&2
  exit 1
fi

if ! git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  echo "Error: not inside a git repository" >&2
  exit 1
fi

if ! command -v gh >/dev/null 2>&1; then
  echo "Error: gh CLI not found in PATH" >&2
  echo "Install GitHub CLI: https://cli.github.com/" >&2
  exit 1
fi

echo "Ensuring current branch is ${MAIN_BRANCH}"
current_branch=$(git symbolic-ref --quiet --short HEAD || echo "")
if [ "$current_branch" != "$MAIN_BRANCH" ]; then
  git checkout "$MAIN_BRANCH"
fi

echo "Fetching latest refs"
git fetch "$REMOTE" --prune

echo "Closing open pull requests"
mapfile -t open_prs < <(gh pr list --state open --json number --jq '.[].number')

if [ "${#open_prs[@]}" -eq 0 ]; then
  echo "No open pull requests found"
else
  for pr in "${open_prs[@]}"; do
    echo "→ Closing PR #${pr}"
    gh pr close "$pr"
  done
fi

echo "Pruning remote branches (remote=${REMOTE})"
while IFS= read -r ref; do
  branch="${ref#refs/remotes/${REMOTE}/}"
  if [ "$branch" = "HEAD" ] || [ "$branch" = "$MAIN_BRANCH" ]; then
    continue
  fi
  echo "→ Deleting remote branch ${REMOTE}/${branch}"
  git push "$REMOTE" --delete "$branch"
done < <(git for-each-ref --format='%(refname)' "refs/remotes/${REMOTE}/")

echo "Pruning local branches"
while IFS= read -r branch; do
  if [ "$branch" = "$MAIN_BRANCH" ]; then
    continue
  fi
  echo "→ Deleting local branch ${branch}"
  git branch -D "$branch"
done < <(git for-each-ref --format='%(refname:short)' refs/heads/)

echo "All done. Remaining branches:"
git branch
