#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd "$SCRIPT_DIR/../.." && pwd)
OUT_DIR="$REPO_ROOT/out/0.45/vscode"
CHECKSUM_FILE="$SCRIPT_DIR/CHECKSUMS.sha256"

node "$REPO_ROOT/tools/vscode-smoke/package-extension.mjs"

(
  cd "$OUT_DIR"
  find . -type f -print0 | sort -z | xargs -0 sha256sum
) >"$CHECKSUM_FILE"

echo "Checksums written to $CHECKSUM_FILE"
