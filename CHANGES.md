# C1 — Changes (Run 001)

## Summary
Implemented an in-memory HTTP host with only `POST /plan` and `POST /apply`. Responses are canonical and cached for idempotency, with proofs emitted only when `DEV_PROOFS=1`.

## Why
Addresses task C1 by providing an ephemeral host that produces stable journal entries and optional proofs as required by END_GOAL.

## Tests
- Added: `packages/host-lite/tests/host-lite.test.ts`
- Updated: n/a
- Determinism/parity: endpoints return canonical bytes; tests run without cross-test bleed.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
