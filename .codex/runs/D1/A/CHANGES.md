# D1 — Changes (Run 1)

## Summary
Implemented a SQLite-backed legal adapter for the Claims API using `sql.js`. Responses now include a canonical BLAKE3 `query_hash`, dataset version, and stable counts with at least ten evidence samples.

## Why
- Align storage with END_GOAL: use SQLite and surface `dataset_version` and canonical BLAKE3 `query_hash` per request.
- Ensure deterministic counts/clauses and ≥10 evidence samples per response.

## Tests
- Added: `services/claims-api-ts/test/d1.sqlite-adapter.test.ts`.
- Determinism/parity: repeated `pnpm test` runs stable; all packages pass.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
