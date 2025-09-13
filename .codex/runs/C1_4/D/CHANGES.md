# C1 — Changes (Run 4)

## Summary
Finalized `host-lite` with a raw JSON handler shared across `/plan` and `/apply`, ensuring canonical bytes and a unified exec path.

## Why
- Completes END_GOAL by delivering deterministic, idempotent endpoints with LRU caching and proof gating.

## Tests
- Added: byte determinism, raw handler 400s, import hygiene, package export guard.
- Updated: multi-world cache bounds now assert map size.
- Determinism/parity: repeated `pnpm test` runs stable; no sockets/files/network.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
