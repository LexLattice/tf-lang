# Observation Log — D1 — Run 1

- Strategy chosen: replace JSON storage with in-memory SQLite via `sql.js`; add BLAKE3 hashing.
- Key changes (files): `services/claims-api-ts/src/server.ts`, `services/claims-api-ts/src/util.ts`, test file.
- Determinism stress (runs × passes): `pnpm test` ×1 (all pass).
- Near-misses vs blockers: initial native deps (`better-sqlite3`, `blake3`) removed to avoid build-script blockers.
- Notes: dataset built per-test to ensure isolation.
