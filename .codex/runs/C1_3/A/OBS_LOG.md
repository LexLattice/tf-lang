# Observation Log — C1 — Run 3

- Strategy chosen: Tightened host-lite with raw handler for 400s and multi-world LRU checks.
- Key changes (files): packages/host-lite/src/server.ts; packages/host-lite/tests/host-lite.test.ts; packages/host-lite/package.json; CHANGES.md; COMPLIANCE.md; OBS_LOG.md; REPORT.md
- Determinism stress (runs × passes): 2×; stable outputs.
- Near-misses vs blockers: ensured tests avoid sockets; added export to test raw parsing.
- Notes: proof hashing skipped when DEV_PROOFS!=1; cache capped at 32 entries/world.
