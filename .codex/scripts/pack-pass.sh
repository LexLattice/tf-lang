#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$ROOT"

SRC_DIR="docs/runs"
OUT_DIR="docs/runs/pack-pass"
mkdir -p "$OUT_DIR"

echo "Packing pass artifacts from $SRC_DIR to $OUT_DIR" >&2
find "$SRC_DIR" -maxdepth 1 -type f -name '*.md' -print0 | while IFS= read -r -d '' f; do
  cp -f "$f" "$OUT_DIR/" || true
done
echo "Done."
