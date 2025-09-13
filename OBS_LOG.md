# Observation Log — C1 — Run 3

- Strategy chosen: Harden host-lite with explicit build outputs, HTTP parsing helper, and expanded tests for error paths and cache bounds.
- Key changes (files): packages/host-lite/src/server.ts; packages/host-lite/tests/host-lite.test.ts; packages/host-lite/package.json; packages/host-lite/tsconfig.json
- Determinism stress (runs × passes): 2×; stable outputs.
- Near-misses vs blockers: `vitest` missing after rename; fixed via install.
- Notes: proof hashing skipped when DEV_PROOFS!=1; cache capped at 32 entries per world with per-world LRU.
