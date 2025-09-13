# C1 — Changes (Run 2)

## Summary
Replaced the Fastify service with a leaf package `packages/host-lite` using only built-in `node:http`. The host now exposes just `POST /plan` and `POST /apply`, serves canonical responses, and bounds in-memory caches.

## Why
Delivers pass-2 goals: clarified packaging, centralized canonicalization, bounded idempotent caching, explicit 404 handling, and removal of third-party HTTP frameworks.

## Tests
- Added: `packages/host-lite/tests/host-lite.test.ts`
- Updated: export surface in `packages/tf-lang-l0-ts/src/index.ts`
- Determinism/parity: repeated tests confirm byte-identical outputs and proof gating.

## Notes
- No schema changes unless explicitly allowed.
- Diffs kept minimal.
