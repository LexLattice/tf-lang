# Dual-stack Template

This template provides paired TypeScript and Rust entrypoints that integrate with `tf-check` for oracle execution.

## Layout

- `ts/src/index.ts` — TypeScript harness invoking tf-check oracles.
- `rust/src/lib.rs` — Rust harness mirroring TypeScript coverage.
- `Makefile` — Convenience targets for running oracles locally.

Copy the template into a fresh branch and wire branch-specific implementations before running CI.
