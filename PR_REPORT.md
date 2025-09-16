## Summary
- Added the `@tf-lang/tf-check` CLI package with schema validation, canonical result formatting, and documentation under `docs/tf-check/USAGE.md`.
- Implemented deterministic execution adapters in TypeScript (`@tf-lang/adapter-execution-ts`) and Rust (`tf-adapters-execution`), plus a parity harness that writes `out/t2/adapter-parity.json`.
- Built the trace→tags mapper and coverage generator packages, emitting canonical artifacts under `out/t2/` and documenting the mapping in `docs/trace-schema.md`.
- Generated all required T2 artifacts in-tree: `tf-check`, adapter trace/parity, `trace-tags.json`, `coverage.json`, and `coverage.html`.
- Wired `t2-runtime.yml` CI workflow with determinism re-runs for each job and artifact uploads.

## Evidence (artifacts re-checked)
- [x] `out/t2/tf-check/help.txt`
- [x] `out/t2/tf-check/result.json`
- [x] `out/t2/adapter-ts-trace.json`
- [x] `out/t2/adapter-parity.json`
- [x] `out/t2/trace-tags.json`
- [x] `out/t2/coverage.json`
- [x] `out/t2/coverage.html`

## Determinism & Seeds
- Repeats: 2 (CLI, adapters, mapper, coverage, Rust tests)
- Seeds: none required (deterministic fixtures only)

## Tests & CI
- TS packages: `pnpm --filter @tf-lang/tf-check run test` ×2, `pnpm --filter @tf-lang/adapter-execution-ts run test` ×3, `pnpm --filter @tf-lang/trace2tags run test` ×2, `pnpm --filter @tf-lang/coverage-generator run test` ×2.
- Rust workspace: `cargo test --workspace --all-targets --manifest-path crates/Cargo.toml` ×2.
- Monorepo build: `pnpm run build`.
- CI: new `t2-runtime` workflow jobs (`tf-check-cli`, `adapter-ts`, `adapter-rust`, `mapper-trace2tags`, `coverage-report`, `adapter-parity`) enforce determinism with double runs.

## Implementation Notes
- No third-party runtime dependencies added; new TypeScript packages rely on Node built-ins and workspace-local code.
- Internal ESM imports use `.js` suffixes; no deep imports between packages.
- All JSON/HTML artifacts are canonical (sorted keys, trailing newline) and regenerated via package scripts.
- Rust adapter uses `BTreeMap` canonicalisation and `thiserror` for deterministic error codes.

## Hurdles / Follow-ups
- Future extensions: expand adapter coverage to additional operations once the schema grows; extend coverage HTML with richer visuals if needed.

### Review batch 2 fixes
- DRY: Introduced `@tf-lang/utils` with canonicalJson/paths/tmp/html helpers; all T2 packages use it.
- Paths: artifact/parity scripts auto-detect repo root (no brittle ../../..).
- Security: `coverage.html` escapes tag/spec values (prevents XSS).
- Robustness: parity harness cleans temp dirs even on error.
- Cleanup: removed dead copyCount logic in TS adapter.
- Consistency: aligned @types/node to ^24.3.1 in all new packages.
- CLI: tf-check flag parsing supports --k=v and rejects unknown flags (no new runtime deps).
- Rust bin: `dump` uses `clap` for argument parsing; README returns `Ok(())`.
- Parity: TS↔Rust traces match (`stepIndex`), parity enforced as a hard gate.
