# C1 — Changes (Run 3)

## Summary
Hardened `host-lite` with canonical error bodies (400 for malformed JSON, 404 otherwise), multi-world LRU cache bounds, and gated proofs with zero overhead when disabled. Package now exports `src/server.ts` directly for clarity.

## Why
- Ensures idempotent, deterministic `/plan` and `/apply` while bounding per-world cache and keeping responses canonical.

## Tests
- Added: extended `packages/host-lite/tests/host-lite.test.ts` for 400/404, multi-world cache caps, packaging and boundary scans.
- Updated: none
- Determinism/parity: repeated runs via `pnpm test` are stable and socket-free.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
