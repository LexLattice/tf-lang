# Observation Log — C1 — Run 2

- Strategy: replace Fastify service with native HTTP handler in a leaf package.
- Key changes: `packages/host-lite/**`, `packages/tf-lang-l0-ts/src/index.ts`, `packages/tf-lang-l0-ts/package.json`, `pnpm-lock.yaml`.
- Determinism stress: repeated plan/apply and 404 routes; cache remained constant.
- Near-misses: build initially emitted tests and missing package entry; fixed tsconfig and package.json.
- Notes: cache stores only last apply per world; no third-party HTTP runtime deps.
