# C1 — Changes (Run 3)

## Summary
Refined `packages/host-lite` as the sole host package with explicit build outputs and centralized HTTP parsing. Added canonical 400/404 errors and expanded LRU tests to cover multi‑world caps.

## Why
- Satisfies END_GOAL: minimal in-memory host with deterministic `/plan` and `/apply` routes and ephemeral state.

## Tests
- Added: `packages/host-lite/tests/host-lite.test.ts` now covers 400/404 errors, multi-world LRU bounds, packaging, and boundary scan.
- Updated: host-lite package build configuration.
- Determinism/parity: repeated runs via `pnpm test` are stable and socket-free.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
