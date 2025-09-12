# C1 — Changes (Run 2)

## Summary
Replaced Fastify host with a bare Node HTTP server packaged under `packages/host-lite`. Added bounded LRU caching and 404 handling to keep responses canonical and idempotent without unbounded growth.

## Why
- Satisfies END_GOAL: minimal in-memory host with deterministic `/plan` and `/apply` routes and ephemeral state.

## Tests
- Added: extended `packages/host-lite/tests/host-lite.test.ts` for idempotency, proof gating, 404s, cache bounds, boundary scan.
- Updated: none
- Determinism/parity: repeated runs via `pnpm test` are stable and socket-free.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
