## 2025-09-15T21:20:58Z
- [C1] Oracle core scaffolding complete for TS & Rust.
- Commands: `pnpm -C packages/oracles/core build`, `pnpm -C packages/oracles/core test`, `cargo test --workspace --all-targets --manifest-path crates/Cargo.toml`.
- Seeds: n/a (unit tests only).

## 2025-09-15T21:45:07Z
- [C2] Determinism oracle implemented in TS/Rust with property tests and fixtures.
- Commands: `pnpm -C packages/oracles/determinism build`, `pnpm -C packages/oracles/determinism test`, `cargo test --workspace --all-targets --manifest-path crates/Cargo.toml`.
- Seeds: TS `0x005a17ce` / `0x009b1d2c`; Rust `0x64657465726d696e69736d2d706173732d736565642d30303030303030303030` / `0x64657465726d696e69736d2d6661696c2d736565642d31313131313131313131`.

## 2025-09-15T23:31:00Z
- [C3] Harmonized determinism fixtures and seeds across TS/Rust; tests now stream fixtures from canonical path.
- Commands: `pnpm -C packages/oracles/determinism build`, `pnpm -C packages/oracles/determinism test`, `cargo test --workspace --all-targets --manifest-path crates/Cargo.toml`.
- Seeds: TS `tests/seeds.json`; Rust `crates/oracles/determinism/tests/seeds.json`.

## 2025-09-15T23:32:00Z
- [C4] Refactored tf-oracles-core internals into canonical/context/oracle/result modules with unchanged API surface.
- Commands: `cargo test --workspace --all-targets --manifest-path crates/Cargo.toml`.
- Seeds: n/a.

## 2025-09-15T23:33:00Z
- [C5] Applied policy polish (Set canonicalization, sorted warnings, BTreeSet dedupe, dev-deps tidy).
- Commands: `pnpm -C packages/oracles/core build`, `pnpm -C packages/oracles/core test`, `pnpm -C packages/oracles-core-ts build`, `pnpm -C packages/oracles-core-ts test`, `cargo test --workspace --all-targets --manifest-path crates/Cargo.toml`.
- Notes: Workspace `pnpm run build` still fails at `services/claims-api-ts` for missing sqlite typings.

## 2025-09-15T23:34:00Z
- [C6] Updated READMEs and TODO for harmonized fixtures, canonical seeds, and determinism notes.
- Commands: n/a (docs only).
- Notes: Fixtures documented under `packages/oracles/determinism/fixtures/`.

## 2025-09-16T00:27:44Z
- [R1] Re-verified determinism packages/builds for PR #110 polish.
- Commands: `pnpm -r --filter './packages/oracles/*' build`, `pnpm -r --filter './packages/oracles/*' test`, `pnpm -r --filter './services/claims-api-ts' test`, `cargo test --workspace --all-targets --manifest-path crates/Cargo.toml`, `pnpm run build`.
- Notes: Seeds unchanged; ambient stubs remain scoped to `services/claims-api-ts`.

## 2025-09-16T00:30:58Z
- [R2] Added ambient stub fence script to enforce policy scope.
- Commands: n/a (script addition only).
- Notes: Script fails if `.d.ts` files appear outside `services/claims-api-ts/src/types/`.

## 2025-09-16T00:32:46Z
- [R3] Tweaked determinism failure return path to use safe conversion API.
- Commands: `cargo fmt --manifest-path crates/oracles/determinism/Cargo.toml`.
- Notes: No public API changes; maintains Result-based flow.

## 2025-09-16T00:34:07Z
- [R4] Compiled PR_REPORT with determinism evidence and follow-ups for PR #110.
- Commands: n/a (documentation only).
- Notes: README TODOs track ambient stub replacement.

## 2025-09-16T01:06:20Z
- [S1] Swapped TS spec adapter to Ajv-backed validation with schema-derived error mapping.
- Commands: n/a (code change only).
- Notes: First non-oneOf Ajv error mapped to existing E_SPEC_* codes.

## 2025-09-16T01:06:46Z
- [S2] Documented serde-based refactor plan in Rust spec adapter for future parity work.
- Commands: n/a (docs only).
- Notes: Parser logic unchanged to keep E_SPEC_* error codes stable.

## 2025-09-16T01:07:09Z
- [S3] Enhanced TS oracles equals/subsetOf for Map/Set support and documented array semantics.
- Commands: n/a (code change only).
- Notes: Added shared canonical helpers under `src/oracles/structures.ts`.

## 2025-09-16T01:07:33Z
- [S4] Hardened build-tasks canonicalizer for nulls and arrays.
- Commands: n/a (script change only).
- Notes: Order preservation unchanged; early null guard added.

## 2025-09-16T01:09:05Z
- [S5] Expanded TS test coverage for Ajv error mapping and Map/Set semantics.
- Commands: n/a (tests only).
- Notes: Added schema edge cases and container-specific oracle checks.

## 2025-09-16T01:20:49Z
- [S6] Re-ran deterministic TS/Rust suites post-rebase and confirmed workspace build.
- Commands: `pnpm -r --filter './packages/oracles/*' test`, `pnpm -r --filter './packages/tf-lang-l0-ts' test`, `pnpm -r --filter './services/claims-api-ts' test`, `cargo test --workspace --all-targets --manifest-path crates/Cargo.toml`, `pnpm run build`.
- Notes: Repeats executed to confirm stability after Ajv/spec updates.

## 2025-09-16T01:46:33Z
- [F1] Updated Rust canonicalizer to rebuild objects via `BTreeMap` and added key-order test.
- Commands: `cargo fmt --manifest-path crates/oracles/core/Cargo.toml`, `cargo test --workspace --all-targets --manifest-path crates/Cargo.toml`.
- Notes: Ensures determinism regardless of serde preserve_order feature.

## 2025-09-16T01:47:03Z
- [F2] Simplified TS spec adapter to rely solely on Ajv error mapping (no pre-checks) with pointer-based selection.
- Commands: `pnpm -r --filter './packages/tf-lang-l0-ts' test`.
- Notes: Added pointer helper to prefer valid ops while keeping existing E_SPEC_* codes.

## 2025-09-16T01:47:36Z
- [F3] Tightened TS subsetOf Map semantics (consume matches) and added duplicate-key coverage.
- Commands: `pnpm -r --filter './packages/oracles/*' test`.
- Notes: equals/subsetOf share canonical helpers for Map/Set ordering.

## 2025-09-16T01:48:17Z
- [F4] Canonical tasks script now encodes Map/Set with deterministic tagging.
- Commands: n/a (script change only).
- Notes: Map/Set tagged with `__kind` to maintain identity in canonical JSON.

## 2025-09-16T01:48:44Z
- [F5] Hardened determinism test repository root discovery with upward search.
- Commands: `cargo fmt --manifest-path crates/oracles/determinism/Cargo.toml`.
- Notes: Stops on `.git` or `pnpm-workspace.yaml` to avoid brittle parent traversal.

## 2025-09-16T01:49:11Z
- [F6] Restored strict Filters typing; added boundary helper and updated tests.
- Commands: `pnpm -r --filter './services/claims-api-ts' test`.
- Notes: `filtersToRecord` now adapts strict Filters for hashing.

## 2025-09-16T01:50:21Z
- [F7] Updated PR_REPORT summary to capture final review fixes.
- Commands: n/a (documentation only).
- Notes: Highlights Ajv migration, BTreeMap canon, Map/Set semantics, and scoped stubs.

## 2025-09-16T02:58:39Z
- [F8] Adjusted CI installs to use workspace root for pnpm.
- Commands: n/a (workflow-only change).
- Notes: Ensures devDependencies (vitest) are available during CI test runs.
