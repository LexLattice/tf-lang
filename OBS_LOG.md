# Observation Log — C1 — Run 1

- Strategy chosen: implement stateless in-memory HTTP host with canonical journal entries and env-gated proofs.
- Key changes (files): services/host-lite-ts/src/server.ts; services/host-lite-ts/tests/host-lite.test.ts.
- Determinism stress (runs × passes): 2× for idempotency in tests.
- Near-misses vs blockers: initial static env check broke proof gating; fixed by runtime check.
- Notes: ensured no filesystem writes and ESM imports include `.js`.
