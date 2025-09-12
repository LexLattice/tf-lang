# Changes

## B2 dev-proof gating
- Cache `DEV_PROOFS` flag in TS and Rust for near-zero production cost.
- Added reset hooks and shared vector to verify parity and caching.
- Tests ensure tags only emit in dev mode and ESM build loads.

### Blockers respected
- No per-call locking on flag check.
- No `static mut`/`unsafe` or `unwrap` on sync primitives.
- Environment isolated via `reset()`.

### New tests
- `packages/tf-lang-l0-ts/tests/proof-dev.test.ts` – "emits expected tags when enabled", "no tags when disabled", "caches env until reset".
- `packages/tf-lang-l0-rs/tests/proof_dev.rs` – "dev_proofs_parity_and_toggle", "dev_proofs_cache_and_reset".
