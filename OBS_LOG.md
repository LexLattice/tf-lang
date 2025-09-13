# Observation Log — C1 — Run 4

- Strategy chosen: Introduced raw JSON handler to centralize parsing and response bytes.
- Key changes (files): packages/host-lite/src/server.ts; packages/host-lite/tests/host-lite.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md.
- Determinism stress (runs × passes): 3×; outputs identical.
- Near-misses vs blockers: ensured deep import sweep covered tests without hitting workspace symlinks.
- Notes: cache map constrained to touched worlds; proof hashing only when DEV_PROOFS=1.
