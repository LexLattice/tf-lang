
#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

# allow skipping via env
if [[ "${GIT_BYPASS_GOLDEN:-0}" == "1" ]]; then
  echo "[golden] bypassed via GIT_BYPASS_GOLDEN=1"
  exit 0
fi

echo "[golden] building claims-core-ts and adapter-legal-ts..."
pnpm -C packages/claims-core-ts build >/dev/null
pnpm -C packages/adapter-legal-ts build >/dev/null

TMP_OUTPUT="$(mktemp)"
trap 'rm -f "$TMP_OUTPUT"' EXIT

echo "[golden] generating current output..."
node packages/adapter-legal-ts/dist/examples/ro-mini/build.js > "$TMP_OUTPUT"

echo "[golden] diffing against .golden/ro-mini.out.txt..."
if diff -u .golden/ro-mini.out.txt "$TMP_OUTPUT" ; then
  echo "[golden] OK: outputs match."
  exit 0
else
  echo ""
  echo "[golden] ERROR: golden output mismatch."
  echo "         If this change is intentional and behavior is truly equivalent,"
  echo "         update the extractor/precedence AND re-justify by adding tests."
  echo "         Do NOT update .golden lightly."
  exit 1
fi
