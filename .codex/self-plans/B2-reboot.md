# Plan for B2-reboot

## Steps
1. Implement DEV_PROOFS caching with reset hook in TS and Rust proof modules.
2. Replace shared global proof logs with AsyncLocalStorage (TS) and thread-local storage (Rust).
3. Export helpers (`withProofLog`, `resetDevProofsForTest`) and ensure imports use `.js` suffix.
4. Update VMs/tests to use new logging APIs; add cache/reset and parallel determinism tests.
5. Add shared `tests/proof-tags.json` and parity tests in TS and Rust.
6. Create `CHANGES.md`, `B2-COMPLIANCE.md`, and append JOURNAL entry.

## Tests
- `pnpm -C packages/tf-lang-l0-ts test`
- `pnpm -C packages/tf-lang-l0-ts build && node -e "import('./packages/tf-lang-l0-ts/dist/proof/index.js')"`
- `cargo test --manifest-path packages/tf-lang-l0-rs/Cargo.toml`

## Risks
- AsyncLocalStorage or thread-local misuse could drop tags or impact performance.
- Environment caching might not reset correctly, causing flaky tests.
- Cross-runtime parity JSON may get out of sync with tag schema.

## Definition of Done
- DEV_PROOFS read once with reset hooks; hot path is constant-time when disabled.
- Proof logs isolated per async/thread context; tests show no leakage.
- Shared vector confirms TS/Rust parity for tags.
- CHANGES, compliance checklist, and JOURNAL updated.
