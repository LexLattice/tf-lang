# Observation Log — C1 — Run 1

- Strategy chosen: Added an in-memory HTTP host with hash-based idempotency and canonical JSON replies.
- Key changes (files): packages/tf-lang-l0-ts/src/host/http-lite.ts; packages/tf-lang-l0-ts/tests/host-lite.test.ts
- Determinism stress (runs × passes): pnpm test (1× pass)
- Near-misses vs blockers: none
- Notes: worlds stored in a Map; proofs flushed per request
