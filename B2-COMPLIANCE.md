# B2 Compliance

- ✅ No per-call locking on flag: cached checks in `packages/tf-lang-l0-ts/src/proof/index.ts` and `packages/tf-lang-l0-rs/src/proof.rs`.
- ✅ No `static mut`/`unsafe`: uses atomics and `thread_local!`.
- ✅ No `unwrap()` on synchronization primitives: none used.
- ✅ No whole-suite serialization: tests run with default parallelism; stateful cases merged.
- ✅ No weakened TS typing: proof modules remain fully typed.
- ✅ No ESM bare imports without extension: all internal imports include `.js`.
- ✅ No magic numbers: `DevProofsState` enum names tri-state cache.
- ✅ No unnecessary cloning on hot paths: tags built only when `devProofsEnabled()` is true.
- ✅ No shared global mutable logs: Rust uses thread-local log; TS cleared via reset hook.
- ✅ No event drops when enabled: `emit` pushes when flag set.
- ✅ No global env bleed across tests: `resetDevProofsForTest`/`reset_for_test` clear cache.
- ✅ Tag schema and hashing rules unchanged: `packages/tf-lang-l0-ts/src/proof/tags.ts` and `packages/tf-lang-l0-rs/src/proof.rs` untouched.
