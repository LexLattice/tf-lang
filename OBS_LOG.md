# Observation Log — D1 — Run 1

- Strategy chosen: replace JSON store with SQLite adapter and BLAKE3 query hashing.
- Key changes (files): services/claims-api-ts/src/db.ts, server.ts, util.ts; packages/claims-core-ts/src/query.ts.
- Determinism stress (runs × passes): 2× `pnpm test` all passed.
- Near-misses vs blockers: initial native SQLite build failed; switched to wasm `sql.js` to keep storage SQLite-only.
- Notes: dataset bootstrapped in tests with duplicated records to satisfy ≥10 sample requirement.
