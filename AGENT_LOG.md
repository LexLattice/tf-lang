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
