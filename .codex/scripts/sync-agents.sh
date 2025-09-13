#!/usr/bin/env bash
set -euo pipefail

SRC=".codex/agents.md"
DST="AGENTS.md"
BEGIN="<!-- BEGIN AGENT:CODER -->"
END="<!-- END AGENT:CODER -->"

extract() {
  awk "/$BEGIN/{flag=1; print; next} /$END/{print; flag=0} flag" "$SRC"
}

gen() {
  cat <<'HDR'
---
# AUTO-GENERATED — do not edit here.
# Source of truth: .codex/agents.md
title: Agents Guide (CODER)
version: 1.0
---
HDR
  echo
  extract
}

case "${1:-}" in
  --check)
    TMP="$(mktemp)"
    gen >"$TMP"
    if ! diff -u "$TMP" "$DST" >/dev/null 2>&1; then
      echo "[agents-sync] Root AGENTS.md is out of date with .codex/agents.md"
      diff -u "$TMP" "$DST" || true
      exit 1
    fi
    echo "[agents-sync] OK"
    ;;
  ""|--write)
    gen >"$DST"
    echo "[agents-sync] wrote $DST from $SRC"
    ;;
  *)
    echo "Usage: $0 [--write|--check]" >&2; exit 2
    ;;
esac
