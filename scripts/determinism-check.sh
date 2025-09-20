#!/usr/bin/env bash
set -euo pipefail
CMD=${1:-"echo no-command"}
TMP1=$(mktemp)
TMP2=$(mktemp)
eval $CMD >/dev/null 2>&1 || true
sha256sum packages/tf-l0-spec/spec/ids.json > "$TMP1" || true
eval $CMD >/dev/null 2>&1 || true
sha256sum packages/tf-l0-spec/spec/ids.json > "$TMP2" || true
diff -u "$TMP1" "$TMP2" && echo "Determinism OK" || (echo "Determinism FAILED" && exit 1)
