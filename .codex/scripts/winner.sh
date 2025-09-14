#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$ROOT"

FILE=".codex/runs/winner/RUNS_REPORTS.md"
if [[ -f "$FILE" ]]; then
  echo "$FILE"
else
  echo "(no winner anthology yet) expected at: $FILE"
fi
