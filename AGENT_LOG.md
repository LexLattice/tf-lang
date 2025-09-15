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
