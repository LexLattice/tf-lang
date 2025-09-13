# Observation Log — C1 — Run 1

- Strategy chosen: Fastify server with canonical JSON caching and in-memory worlds.
- Key changes (files): services/host-lite/src/server.ts; services/host-lite/tests/host-lite.test.ts; pnpm-lock.yaml
- Determinism stress (runs × passes): 2×; stable outputs.
- Near-misses vs blockers: initial response order broke idempotency; fixed by returning canonical JSON.
- Notes: DEV_PROOFS toggled in tests to verify gating.
