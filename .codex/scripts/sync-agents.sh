#!/usr/bin/env bash
set -euo pipefail

IDX=".codex/agent-index.yml"
ROOT="AGENTS.md"
OUT="$ROOT"
CHECK=0

for arg in "$@"; do
  case "$arg" in
    --check)
      CHECK=1
      ;;
    *)
      ;;
  esac
done

command -v yq >/dev/null 2>&1 || { echo "Requires 'yq' (https://github.com/mikefarah/yq)"; exit 1; }

# Prepare output target
if [[ "$CHECK" -eq 1 ]]; then
  OUT="${ROOT}.check"
  # Seed OUT with current AGENTS.md if present
  if [[ -f "$ROOT" ]]; then
    cp -f "$ROOT" "$OUT"
  else
    : > "$OUT"
  fi
fi

# Read role map
mapfile -t ROLES < <(yq -r '.roles | keys[]' "$IDX")

# Ensure OUT exists with container markers
if ! grep -q 'SYNTHESIZED ROLE BLOCKS' "$OUT" 2>/dev/null; then
  cat >"$OUT" <<'HDR'
---
title: Agents Guide (multi-role)
version: 1.0
---

**Applicability:** This file is only used when a prompt explicitly names a role (e.g., `AGENT:CODER_CLI` or `AGENT:CODER_CLOUD`). Otherwise, ignore it.

> Do not edit the blocks below by hand. Run `.codex/scripts/sync-agents.sh` to refresh from `.codex/agents/*`.

<!-- =========================  SYNTHESIZED ROLE BLOCKS  ========================= -->

<!-- =========================  END SYNTHESIZED BLOCKS  ========================= -->
HDR
fi

# Replace or insert each block into OUT (no extra header; body controls headings)
for role in "${ROLES[@]}"; do
  start=$(yq -r ".roles.\"$role\".start" "$IDX")
  end=$(yq -r ".roles.\"$role\".end" "$IDX")
  src=$(yq -r ".roles.\"$role\".source" "$IDX")
  # Basic sanitization for accidental quotes
  src=${src%\"}
  src=${src#\"}

  [[ -f "$src" ]] || { echo "Missing source: $src"; exit 1; }
  body=$(cat "$src")
  block=$"$body\n"

  if grep -qF "$start" "$OUT"; then
    # Replace between markers
    awk -v s="$start" -v e="$end" -v b="$block" '
      BEGIN{printing=1}
      $0 ~ s {print $0; print b; skip=1; printing=0; next}
      $0 ~ e {printing=1}
      printing && !skip {print $0}
      $0 ~ e {print $0; skip=0}
    ' "$OUT" > "$OUT.tmp" && mv "$OUT.tmp" "$OUT"
  else
    # Insert before END container
    awk -v s="$start" -v e="$end" -v b="$block" '
      /END SYNTHESIZED BLOCKS/ { print s ORS b ORS e; }
      { print }
    ' "$OUT" > "$OUT.tmp" && mv "$OUT.tmp" "$OUT"
  fi
  echo "[sync] updated block $role ← $src"
done

if [[ "$CHECK" -eq 1 ]]; then
  if ! diff -u "$ROOT" "$OUT" >/dev/null 2>&1; then
    echo "[sync] AGENTS.md is out-of-sync with sources (.codex/agents/*):"
    diff -u "$ROOT" "$OUT" || true
    rm -f "$OUT"
    exit 1
  fi
  echo "[sync] OK: AGENTS.md is up to date"
  rm -f "$OUT"
else
  echo "[sync] done → $OUT"
fi
