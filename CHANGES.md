# C1 — Changes (Run 1)

## Summary
Implemented an in-memory HTTP host exposing only `POST /plan` and `POST /apply`, returning canonical journal entries and gating proofs behind `DEV_PROOFS`.

## Why
Meets the END_GOAL for C1 by providing idempotent, ephemeral world operations with deterministic outputs.

## Tests
- Added: services/host-lite-ts/tests/host-lite.test.ts
- Updated: none
- Determinism/parity: `pnpm test` verifies repeated calls yield identical responses.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
