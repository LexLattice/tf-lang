# B2 Compliance

- ✅ No per-call locking on env check: `packages/tf-lang-l0-rs/src/proof.rs`, `packages/tf-lang-l0-ts/src/proof/index.ts`.
- ✅ No `static mut`/`unsafe`: safe globals only.
- ✅ No `unwrap()` on sync primitives: `packages/tf-lang-l0-rs/src/proof.rs` uses match/expect.
- ✅ No whole-suite test serialization: tests run parallel with isolated state.
- ✅ No weakened TypeScript typing: strict `ProofTag` types and env logic.
- ✅ No ESM bare imports without extension: all internal imports include `.js`.
- ✅ No magic numbers: named helpers manage cache.
- ✅ No unnecessary cloning/copying on hot paths: tags pushed by reference.
- ✅ No shared mutable logs leaking across tests: `reset()` clears state.
- ✅ No dev logging drop when enabled: `emit` always records when flag true.
- ✅ Env influence isolated: tests set/unset `DEV_PROOFS` and call `reset()`.
- ✅ Tag schema and hashing rules unchanged.
