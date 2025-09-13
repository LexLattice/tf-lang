# Observation Log — C1 — Run 4

- Strategy chosen: Finalized host-lite with raw JSON handler; unified exec path and Node server wiring.
- Key changes (files): packages/host-lite/src/server.ts; packages/host-lite/tests/host-lite.test.ts; CHANGES.md; COMPLIANCE.md; REPORT.md
- Determinism stress (runs × passes): 2×; stable outputs.
- Near-misses vs blockers: ensured import sweep excluded tests to avoid false positives; mocked hashing to verify gating.
- Notes: blake3 hashing counted to prove zero-cost gating; per-world cache map size asserted.
