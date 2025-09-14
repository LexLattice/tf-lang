#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$ROOT"

OUT_DIR="docs/runs"
OUT_FILE="$OUT_DIR/pass-report.md"
mkdir -p "$OUT_DIR"

echo "# Pass Report" > "$OUT_FILE"
printf "_Generated: %(%Y-%m-%d %H:%M:%S UTC)T_\n\n" -1 >> "$OUT_FILE"
if [[ -n "${GROUP:-}" ]]; then
  echo "- Group: $GROUP" >> "$OUT_FILE"
fi
if [[ -n "${PRS:-}" ]]; then
  echo "- PRs: $PRS" >> "$OUT_FILE"
fi

echo "Wrote $OUT_FILE"
