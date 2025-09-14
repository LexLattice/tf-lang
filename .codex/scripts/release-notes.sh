#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$ROOT"

OUT_DIR="docs/runs"
OUT_FILE="$OUT_DIR/release-notes.md"
SRC="docs/archive/v0.2/CHANGES.md"
mkdir -p "$OUT_DIR"

{
  echo "# Release Notes (draft)"
  printf "_Generated: %(%Y-%m-%d %H:%M:%S UTC)T_\n\n" -1
  if [[ -f "$SRC" ]]; then
    echo "(Sourced from $SRC)"
    echo
    sed -n '1,120p' "$SRC" || true
  else
    echo "No archive found at $SRC; add highlights here."
  fi
} > "$OUT_FILE"

echo "Wrote $OUT_FILE"
