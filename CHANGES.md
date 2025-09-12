# Changes

## B2 – Dev-only proof tags with cached env

### Approach
- Cache `DEV_PROOFS` flag once with reset hooks in TypeScript and Rust.
- Isolate proof logs using `AsyncLocalStorage` (TS) and `thread_local!` (Rust).
- Shared parity vector verifies identical tags across runtimes.

### Blockers Respected
- No per-call locking on flag lookup.
- No `static mut` or `unsafe`.
- No `unwrap` on synchronization primitives.
- No whole-suite test serialization.
- No weakened TypeScript typing.
- All internal ESM imports include the `.js` suffix.
- No magic numbers; descriptive names used.
- No unnecessary cloning on hot paths.
- No shared global mutable proof logs; per-context storage prevents leakage.
- Dev logging fails loudly if context missing when enabled.
- Environment influence isolated via reset hooks.
- Tag schemas and hashing rules unchanged.

### New Tests
- `packages/tf-lang-l0-ts/tests/proof-dev.test.ts`
  - emits tags when DEV_PROOFS=1
  - no tags when DEV_PROOFS is unset
  - caches env and supports reset
  - parallel logs are isolated
  - matches shared vector tags
  - shared vector emits no tags when disabled
- `packages/tf-lang-l0-rs/tests/proof_dev.rs`
  - dev_proofs_toggle
  - cache_and_reset
  - parallel_logs_isolated
  - shared_vector_parity
