# C1 — Changes (Run 4)

## Summary
Finalized `host-lite` with a raw JSON handler and canonical Node server wiring. Responses are byte-stable, proofs remain gated, and per-world caches stay bounded.

## Why
- Consolidates plan/apply exec path and centralizes JSON parsing for deterministic error and data handling.

## Tests
- Added: raw handler determinism, proof gating counts, route/method 404s, malformed JSON 400, multi-world LRU map-size check, import sweep.
- Determinism/parity: repeated `pnpm -F host-lite-ts test` runs stable; no sockets/network.

## Notes
- No schema changes; no new runtime deps.
