Task: B2-nits — Review nits for PR #33 (no behavior changes)

Goal
- Clarify Rust `dev_proofs_enabled` control flow (linearize logic)
- Remove TS `as any` by using a const tuple assertion

Steps
1) Edit Rust `packages/tf-lang-l0-rs/src/proof.rs` function body
2) Edit TS `packages/tf-lang-l0-ts/src/vm/interpreter.ts` emit line
3) Build TS package and run TS tests and vectors
4) Run Rust tests (unit + vectors)

Tests
- TS: `pnpm -C packages/tf-lang-l0-ts build && pnpm -C packages/tf-lang-l0-ts test && pnpm -C packages/tf-lang-l0-ts vectors`
- Rust: `cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml --tests -- --nocapture`
- Determinism: Compare TS/Rust vector reports via `.codex/compare-reports.mjs`

Risks
- None; changes are refactors only. Ensure ESM imports remain `.js` and type assertions are correct.

Definition of Done
- Code compiles in TS and Rust
- All tests pass; vector reports match
- No behavior or API changes beyond type-level cleanup
