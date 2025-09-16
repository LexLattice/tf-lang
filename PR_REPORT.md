# PR #110 — Final Polish Summary

## Summary
- TS spec adapter now delegates validation to Ajv against `schema/tf-spec.schema.json`, mapping the first relevant validation error to the existing `E_SPEC_*` codes (including branch-specific param errors and op/version checks).
- Rust spec adapter behaviour is unchanged; added TODO documenting the future serde-based refactor while keeping the explicit error mapping today.
- Rust canonicalization now rebuilds objects through `BTreeMap` to preserve ordering regardless of serde settings.
- TS spec adapter relies solely on Ajv + mapError; Rust adapter documents the serde follow-up while keeping error codes stable.
- TS oracles `equals`/`subsetOf` gained Map/Set semantics with canonical sorting and README notes; `.codex/scripts/build-tasks-json.mjs` canon is now null-safe and Map/Set aware.
- Scoped ambient stubs remain confined to `services/claims-api-ts/src/types/`, enforced by `scripts/check-ambient-stubs.sh`; service filters stay strictly typed via boundary helpers.
- Scoped ambient stubs remain confined to `services/claims-api-ts/src/types/`, enforced by `scripts/check-ambient-stubs.sh`.

## Not Changed
- Public exports for `@tf/oracles-*` packages and `tf-oracles-*` crates remain untouched.
- No new runtime dependencies were introduced; Ajv already ships in the workspace and is reused here.

## Evidence (artifacts)
- determinism fixtures: `packages/oracles/determinism/fixtures/*.json`
- seeds: `packages/oracles/determinism/tests/seeds.json`, `crates/oracles/determinism/tests/seeds.json`

## Determinism & Seeds
- Repeats: 2 (`pnpm -r --filter "./packages/oracles/*" test` run twice, `cargo test --workspace --all-targets` run twice).
- Seeds unchanged; recorded in the seed JSON files above.

## Tests & CI
- `pnpm -r --filter "./packages/oracles/*" build`
- `pnpm -r --filter "./packages/oracles/*" test` (6 + 7 tests per run, repeated twice)
- `pnpm -r --filter "./packages/tf-lang-l0-ts" test` (26 tests, repeated twice)
- `pnpm -r --filter "./services/claims-api-ts" test` (10 tests, repeated twice)
- `cargo test --workspace --all-targets --manifest-path crates/Cargo.toml` (repeated twice)
- `pnpm run build`
- Optional guard: `scripts/check-ambient-stubs.sh` ensures scoped stubs.

## Implementation Notes
- Ajv validation is scoped to the new spec adapter implementation; the rest of the package surface remains unchanged.
- Rust libraries contain no `unwrap()`/panicking paths; dedupe logic relies on `BTreeSet` for deterministic ordering.
- Map/Set canonicalisation relies on local helpers with deterministic sorting; arrays remain structural deep-partials as documented.
- Ambient type stubs remain confined to `services/claims-api-ts/src/types/` with TODOs documenting replacement work.

## Hurdles / Follow-ups
- [ ] Replace ambient sql.js types (tracked in `services/claims-api-ts/README.md`).
- [ ] Replace ambient @tf-lang/d1-sqlite types (tracked in `services/claims-api-ts/README.md`).
- Optional future work: wire `scripts/check-ambient-stubs.sh` into CI as a warning job.
