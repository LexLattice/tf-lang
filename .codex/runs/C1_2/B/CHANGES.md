# C1 — Changes (Run 2)

## Summary
Refactored the Fastify host service into a leaf package (`packages/host-lite`) using
native HTTP primitives. The package exposes only `POST /plan` and `POST /apply`,
centralizes canonical JSON and proof hashing, bounds idempotent caching, and
returns 404 for any other path.

## Why
- Aligns with Pass‑2 goals: single host package, deterministic canonicalization,
idempotency without unbounded growth, and optional proofs.

## Tests
- Added: `packages/host-lite/tests/host-lite.test.ts`
- Updated: `packages/tf-lang-l0-ts/src/index.ts`
- Determinism/parity: repeated runs yield byte‑identical responses and constant cache size.

## Notes
- Removed Fastify; no third‑party runtime HTTP dependencies.
