# C1 — Changes (Run 4)

## Summary
Added `makeRawHandler` to parse raw JSON and share exec path, wired `createServer` through it for canonical byte responses, and expanded tests for determinism, cache sizing, import hygiene, and package exports.

## Why
- Finalizes host-lite endpoint behavior with explicit JSON parsing, idempotent plan/apply outputs, and per-world LRU.

## Tests
- Added: raw handler 400s, byte-identical plan/apply, cache map size, import sweep, package export check.
- Updated: proof gating, multi-world cache bounds.
- Determinism/parity: repeated `pnpm -F host-lite-ts test` runs stable; no sockets/files/network.

## Notes
- No schema changes.
- Diffs kept minimal.
