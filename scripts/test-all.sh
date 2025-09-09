#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[tests] starting TypeScript & Rust test suites..."

if command -v pnpm >/dev/null 2>&1; then
  pnpm -C packages/tf-lang-l0-ts test || { echo "[tests] TS tests failed"; exit 1; }
else
  echo "[tests] pnpm not found; skipping TS tests"
fi

if command -v cargo >/dev/null 2>&1; then
  cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml || { echo "[tests] Rust tests failed"; exit 1; }
else
  echo "[tests] cargo not found; skipping Rust tests"
fi

echo "[tests] all done."
