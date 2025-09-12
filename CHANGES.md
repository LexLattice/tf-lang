# Changes

## B2
- Added cached `DEV_PROOFS` flag with test reset hooks in TypeScript and Rust.
- Rust logs are thread-local; TS caches env and emits only when enabled.
- Tests cover enable/disable, cache warm/cold reset, parallel isolation, vector parity, and ESM build.
- Blockers respected:
  - no per-call locking or unsafe state
  - no `unwrap()` on sync primitives
  - no cross-test leakage via thread-local logs
  - all internal imports use `.js` extensions

### Tests Added
- `packages/tf-lang-l0-ts/tests/proof-dev.test.ts` – `caches env and resets`
- `packages/tf-lang-l0-ts/tests/proof-vector.test.ts` – vector parity
- `packages/tf-lang-l0-ts/tests/esm-build.test.ts` – Node ESM load
- `packages/tf-lang-l0-rs/tests/proof_dev.rs` – `dev_proofs_toggles_tags`, `caches_env_and_resets`, `parallel_logs_isolated`, `vector_parity`
