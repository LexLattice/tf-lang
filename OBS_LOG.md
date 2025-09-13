# Observation Log — C1 — Run 3

- Strategy chosen: Hardened host-lite error paths and cache proofs while maintaining zero-dep runtime.
- Key changes (files): packages/host-lite/src/server.ts; packages/host-lite/tests/host-lite.test.ts; packages/host-lite/package.json
- Determinism stress (runs × passes): 3×; stable outputs.
- Near-misses vs blockers: boundary scan kept local to host-lite to avoid false positives.
- Notes: proofs hashed only when DEV_PROOFS=1; per-world cache capped at 32.
