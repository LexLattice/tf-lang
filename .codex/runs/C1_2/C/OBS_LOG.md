# Observation Log — C1 — Run 2

- Strategy chosen: remove Fastify; custom `node:http` host with bounded cache and public L0 exports.
- Key changes (files): packages/host-lite/src/server.ts; packages/host-lite/tests/host-lite.test.ts; packages/tf-lang-l0-ts/src/index.ts; pnpm-lock.yaml
- Determinism stress (runs × passes): 2×; stable outputs and 404 coverage.
- Near-misses vs blockers: package import failed until `tf-lang-l0` exported `DummyHost`.
- Notes: cache capped at 16 entries to avoid growth; DEV_PROOFS toggled in tests.
