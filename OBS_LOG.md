# Observation Log — C1 — Run 4

- Strategy chosen: Introduced raw JSON handler, unified server path, and broadened tests for imports and cache sizing.
- Key changes (files): packages/host-lite/src/server.ts; packages/host-lite/tests/host-lite.test.ts; CHANGES.md; COMPLIANCE.md; OBS_LOG.md; REPORT.md
- Determinism stress (runs × passes): 3×; stable outputs.
- Near-misses vs blockers: updated glob syntax to avoid warnings; ensured tests avoid FS/network.
- Notes: proofs hashed only when DEV_PROOFS=1; per-world cache capped at 32; cache map equals worlds touched.
