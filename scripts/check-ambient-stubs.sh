#!/usr/bin/env bash
set -euo pipefail

# Warn if new ambient declaration stubs appear outside the scoped service directory.
violations=$(git ls-files "**/*.d.ts" | grep -v '^services/claims-api-ts/src/types/' || true)
if [[ -n "$violations" ]]; then
  echo "Found .d.ts stubs outside claims-api-ts service:" >&2
  echo "$violations" >&2
  exit 1
fi
