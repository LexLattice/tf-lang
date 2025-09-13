# C1 — Changes (Run 1)

## Summary
Implemented an in-memory Fastify host exposing only `POST /plan` and `POST /apply`,
ensuring idempotent requests and canonical journals with optional proofs.

## Why
- Satisfies END_GOAL: minimal HTTP host with ephemeral state and proof gating.

## Tests
- Added: `services/host-lite/tests/host-lite.test.ts`
- Updated: none
- Determinism/parity: repeated runs yield identical responses and reset state.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
