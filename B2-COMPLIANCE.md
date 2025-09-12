# B2 Compliance

- ✅ No per-call locking on flag lookup — `cached` / `OnceCell` caches env (`packages/tf-lang-l0-ts/src/proof/index.ts`, `packages/tf-lang-l0-rs/src/proof.rs`).
- ✅ No `static mut` or `unsafe` — uses `AsyncLocalStorage` and `thread_local!` (`packages/tf-lang-l0-ts/src/proof/index.ts`, `packages/tf-lang-l0-rs/src/proof.rs`).
- ✅ No `unwrap` on synchronization primitives — thread-local `RefCell` and async storage require none (`packages/tf-lang-l0-rs/src/proof.rs`).
- ✅ No whole-suite test serialization — concurrency tested via `Promise.all` and `thread::scope` (`packages/tf-lang-l0-ts/tests/proof-dev.test.ts`, `packages/tf-lang-l0-rs/tests/proof_dev.rs`).
- ✅ No weakened TypeScript typing — strict types in proofs and tests (`packages/tf-lang-l0-ts/src/proof/index.ts`).
- ✅ ESM imports include `.js` suffix — e.g., `../src/vm/index.js` (`packages/tf-lang-l0-ts/tests/proof-dev.test.ts`).
- ✅ No magic numbers — descriptive names for all states (`packages/tf-lang-l0-ts/src/proof/index.ts`).
- ✅ No unnecessary cloning — logs push references only (`packages/tf-lang-l0-ts/src/proof/index.ts`, `packages/tf-lang-l0-rs/src/proof.rs`).
- ✅ No shared global mutable logs — per-context storage (`packages/tf-lang-l0-ts/src/proof/index.ts`, `packages/tf-lang-l0-rs/src/proof.rs`).
- ✅ No event loss when enabled — `emit` throws if context missing (`packages/tf-lang-l0-ts/src/proof/index.ts`).
- ✅ Environment isolation via reset hooks — `resetDevProofsForTest` functions (`packages/tf-lang-l0-ts/src/proof/index.ts`, `packages/tf-lang-l0-rs/src/proof.rs`).
- ✅ Tag schema unchanged — only logging infrastructure touched.
