#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$ROOT"

OUT_DIR="docs/runs"
OUT_FILE="$OUT_DIR/knowledge.md"
SRC_DIR=".codex/knowledge"
mkdir -p "$OUT_DIR"

{
  echo "# Knowledge Index"
  printf "_Generated: %(%Y-%m-%d %H:%M:%S UTC)T_\n\n" -1
  find "$SRC_DIR" -maxdepth 1 -type f -name '*.md' -printf '- %f\n' 2>/dev/null | sort || true
} > "$OUT_FILE"

echo "Wrote $OUT_FILE"
