# C1 — Changes (Run 2)

## Summary
Moved the host to a single `packages/host-lite` leaf package and replaced Fastify with a
minimal `node:http` implementation exposing only `POST /plan` and `POST /apply`. Responses
are canonically serialized, proof emission is gated by `DEV_PROOFS`, and caches are bounded
to avoid memory growth.

## Why
- Aligns with END_GOAL and pass‑2 targets: centralized canonicalization, bounded idempotent
behaviour, and dependency‑slim runtime.

## Tests
- Added: `packages/host-lite/tests/host-lite.test.ts`
- Updated: `packages/tf-lang-l0-ts/src/index.ts`
- Determinism/parity: repeated calls yield byte‑identical outputs; 404 paths handled.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
