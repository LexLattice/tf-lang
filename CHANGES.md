# D1 — Changes (Run 1)

## Summary
Implemented a SQLite-backed legal adapter and rewired the claims API to use it for count and clause queries. Responses now emit BLAKE3 `query_hash`es and dataset versions with stable sample counts.

## Why
- EG: Claims API uses SQLite adapter for counts/clauses.
- EG: Responses include `dataset_version` and canonical BLAKE3 `query_hash`.
- EG: Counts/clauses stable with ≥10 evidence samples.

## Tests
- Added: `services/claims-api-ts/test/sqlite.test.ts`.
- Updated: n/a.
- Determinism/parity: repeated runs of `pnpm test` stable.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
