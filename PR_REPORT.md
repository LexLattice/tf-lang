# PR #110 — Final Polish Summary

## Summary
- Re-confirmed determinism fixtures and seeds wired through both runtimes; reran builds/tests twice to ensure stability without altering public APIs.
- Added a scoped policy guard (`scripts/check-ambient-stubs.sh`) and tightened determinism error flow to rely on safe `Result` conversion.
- Documented the temporary ambient stubs in the claims API service README and TODO checkboxes; no runtime dependencies changed.

## Not Changed
- Public exports for `@tf/oracles-*` packages and `tf-oracles-*` crates remain untouched.
- No new workflows or runtime dependencies were introduced; ambient stubs stay local to `services/claims-api-ts`.

## Evidence (artifacts)
- determinism fixtures: `packages/oracles/determinism/fixtures/*.json`
- seeds: `packages/oracles/determinism/tests/seeds.json`, `crates/oracles/determinism/tests/seeds.json`

## Determinism & Seeds
- Repeats: 2 (`pnpm -r --filter "./packages/oracles/*" test` run twice, `cargo test --workspace --all-targets` run twice).
- Seeds unchanged; recorded in the seed JSON files above.

## Tests & CI
- `pnpm -r --filter "./packages/oracles/*" build`
- `pnpm -r --filter "./packages/oracles/*" test`
- `pnpm -r --filter "./services/claims-api-ts" test`
- `cargo test --workspace --all-targets --manifest-path crates/Cargo.toml`
- `pnpm run build`
- Optional guard: `scripts/check-ambient-stubs.sh` ensures scoped stubs.

## Implementation Notes
- Confirmed all internal TS ESM imports use `.js` suffixes; no deep cross-package imports or `as any` in production code touched by PR.
- Rust libraries contain no `unwrap()`/panicking paths; dedupe logic relies on `BTreeSet` for deterministic ordering.
- Ambient type stubs remain confined to `services/claims-api-ts/src/types/` with TODOs documenting replacement work.

## Hurdles / Follow-ups
- [ ] Replace ambient sql.js types (tracked in `services/claims-api-ts/README.md`).
- [ ] Replace ambient @tf-lang/d1-sqlite types (tracked in `services/claims-api-ts/README.md`).
- Optional future work: wire `scripts/check-ambient-stubs.sh` into CI as a warning job.
