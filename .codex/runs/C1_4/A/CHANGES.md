# C1 — Changes (Run 4)

## Summary
Finalized `host-lite` with a raw JSON handler to unify `/plan` and `/apply`, enforcing canonical bytes and stricter error paths.

## Why
- Delivers deterministic, idempotent planning/apply with per-world LRU and proof gating.

## Tests
- Added: byte determinism, DEV_PROOFS gating, deep import sweep, package export guard.
- Updated: cache bounds to track world count, consolidated error checks.
- Determinism/parity: repeated `pnpm -F host-lite-ts test` runs stable; no sockets/network.

## Notes
- In-memory only; no new runtime deps.
