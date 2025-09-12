# Observation Log — C1 — Run 001

- Strategy chosen: in-memory Node HTTP server with cached plan/apply.
- Key changes (files): `packages/host-lite/src/index.ts`, `packages/host-lite/tests/host-lite.test.ts`.
- Determinism stress (runs × passes): 2× `pnpm test` runs locally.
- Near-misses vs blockers: fixed relative `.js` imports for ESM compliance.
- Notes: proofs hashed via BLAKE3 when enabled.
