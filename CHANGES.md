# D1 — Changes (Run 1)

## Summary
- Added SQLite-backed adapter and canonical BLAKE3 query hashing for Claims API.
- Responses now expose dataset versions, stable hashes, and return at least ten evidence samples.

## Why
- Satisfies D1 end goal: SQLite storage ensures deterministic counts and clause retrieval.
- Canonical hashing (BLAKE3) stabilizes queries across repeated runs.

## Tests
- Added: services/claims-api-ts/test/sqlite.test.ts.
- Updated: packages/claims-core-ts/src/query.ts sample size to 10.
- Determinism/parity: repeated runs yield identical counts and samples.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
