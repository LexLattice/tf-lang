# C1 — Changes (Run 3)

## Summary
Refined `host-lite` to enforce canonical error handling and deterministic responses. Added raw request parsing with 400/404 coverage, multi-world LRU bounds, and packaging exports for clarity.

## Why
- Meets END_GOAL by keeping host minimal while ensuring idempotent, bounded `/plan` and `/apply` with canonical bytes.

## Tests
- Added: `packages/host-lite/tests/host-lite.test.ts` now checks 400/404 models, multi-world cache bounds, and byte-level determinism.
- Updated: none
- Determinism/parity: `pnpm test` repeats are stable and avoid sockets/files.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
