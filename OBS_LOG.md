# Observation Log — C1 — Run 2

- Strategy chosen: replaced Fastify with native `node:http`; wrapped logic in leaf package with bounded caches.
- Key changes (files): packages/host-lite/src/index.ts; packages/host-lite/tests/host-lite.test.ts; packages/tf-lang-l0-ts/src/index.ts
- Determinism stress (runs × passes): tests repeated 2×; outputs stable.
- Near-misses vs blockers: had to add `exports` field to `tf-lang-l0` to avoid deep imports.
- Notes: cache limit keeps memory bounded; dependency surface minimized.
