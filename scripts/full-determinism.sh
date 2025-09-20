#!/usr/bin/env bash
set -euo pipefail
CMD=${1:-""}
if [ -z "$CMD" ]; then
  echo "Usage: scripts/full-determinism.sh '<cmd>'"
  exit 2
fi
digest_all() {
  local OUT=$1
  find out/0.4 packages/tf-l0-spec/spec -type f -print0 2>/dev/null | sort -z | xargs -0 sha256sum > "$OUT" || true
}
rm -rf out/0.4 || true
eval "$CMD" >/dev/null 2>&1 || true
TMP1=$(mktemp); digest_all "$TMP1"
rm -rf out/0.4 || true
eval "$CMD" >/dev/null 2>&1 || true
TMP2=$(mktemp); digest_all "$TMP2"
echo "Comparing digests:"
if diff -u "$TMP1" "$TMP2"; then echo "Full determinism OK"; else echo "Full determinism FAILED"; exit 1; fi
