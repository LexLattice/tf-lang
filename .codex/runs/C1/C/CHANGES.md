# C1 — Changes (Run 1)

## Summary
Implemented a minimal in-memory HTTP host exposing only `POST /plan` and `POST /apply`. Responses are canonical and idempotent, with optional proof tags when `DEV_PROOFS=1`. World state remains ephemeral.

## Why
- Minimal host with idempotent endpoints and canonical journals fulfils the C1 end goal.

## Tests
- Added: `packages/tf-lang-l0-ts/tests/host-lite.test.ts`
- Updated: none
- Determinism/parity: repeated HTTP calls return byte-identical responses; tests run in isolated servers.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
