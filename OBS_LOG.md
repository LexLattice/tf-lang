# Observation Log — D1 — Run 1

- Strategy chosen: wrap `sqlite3` CLI for adapter to keep runtime pure SQLite and deterministic.
- Key changes (files): `packages/adapter-legal-ts/src/sqlite.ts`, `services/claims-api-ts/src/server.ts`, `services/claims-api-ts/src/util.ts`.
- Determinism stress (runs × passes): `pnpm test` ×2 passes.
- Near-misses vs blockers: initial native bindings rejected; switched to CLI approach.
- Notes: query hashing uses `@noble/hashes` BLAKE3; samples fixed at 10.
