# Observation Log — C1 — Run 2

- Strategy chosen: Migrated host to package with Node HTTP server and LRU cache.
- Key changes (files): packages/host-lite/src/server.ts; packages/host-lite/tests/host-lite.test.ts; packages/tf-lang-l0-ts/src/index.ts; pnpm-lock.yaml
- Determinism stress (runs × passes): 2×; stable outputs.
- Near-misses vs blockers: needed package export to avoid deep imports.
- Notes: proof hashing skipped when DEV_PROOFS!=1; cache capped at 32 entries per world.
