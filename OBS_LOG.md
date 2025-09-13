# Observation Log — C1 — Run 3

- Strategy chosen: Tightened host-lite surface with centralized JSON canonicalization and explicit error paths.
- Key changes (files): packages/host-lite/src/server.ts; packages/host-lite/tests/host-lite.test.ts; packages/host-lite/package.json
- Determinism stress (runs × passes): 3×; stable outputs.
- Near-misses vs blockers: ensuring hermetic 400 test without sockets required optional body in handler.
- Notes: per-world cache cap retained at 32; proofs hashed only when `DEV_PROOFS=1`.
