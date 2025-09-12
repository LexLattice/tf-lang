# Changes

## B2 - Dev-only proof tags with caching
- Cached `DEV_PROOFS` flag with reset hook in TS and Rust.
- Thread-local proof logs in Rust and module-scoped log reset in TS.
- VMs guard tag construction with `devProofsEnabled` for zero overhead when disabled.
- Added shared proof tag vector for cross-runtime parity.

### Blockers respected
- Environment flag read once and cached; no per-call locking.
- No `unsafe` or `static mut`; used atomics and thread-local storage.
- Synchronization primitives avoid `unwrap`; no mutexes on hot paths.
- Maintained strict typings and `.js` ESM imports.

### New tests
- `packages/tf-lang-l0-ts/tests/proof-dev.test.ts` – cache and toggle behaviour.
- `packages/tf-lang-l0-ts/tests/proof-vector.test.ts` – parity with vector.
- `packages/tf-lang-l0-rs/tests/proof_dev.rs` – cache and toggle behaviour.
- `packages/tf-lang-l0-rs/tests/proof_vector.rs` – parity with vector.
