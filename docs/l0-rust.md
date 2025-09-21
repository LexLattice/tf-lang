# L0 Rust code generation

This repository includes an experimental Rust code generator that mirrors the TypeScript in-memory runtime. The generated crates contain deterministic in-memory adapters, a reusable IR runner, and a `run` binary that can execute an IR file and emit trace lines compatible with `trace.v0.4`.

## Quickstart

```bash
pnpm run codegen:rs:signing
```

The helper script copies the IR into a fresh crate, writes deterministic sources under `src/`, and produces a `Cargo.toml` with the required dependencies. Re-running the generator overwrites files with identical content, making regeneration safe.

## Running the generated binary locally

When a Rust toolchain is available, opt in with `LOCAL_RUST=1` to build and run the generated crate immediately. The helper script forwards the IR path and captures the emitted trace under the crate's `out/` directory; otherwise the generation step completes without touching `cargo`.

```bash
LOCAL_RUST=1 cargo run --manifest-path out/0.4/codegen-rs/signing/Cargo.toml -- --ir out/0.4/ir/signing.ir.json
```

## Trace parity with TypeScript

```bash
pnpm run parity:ts-rs:signing
```

The parity script regenerates the signing IR, writes both the canonical JSON and the Rust crate, and runs the TypeScript runtime to emit `out/0.4/traces/ts.jsonl`. When `LOCAL_RUST=1` it additionally builds the Rust crate, emits `out/0.4/traces/rs.jsonl`, and verifies that the ordered `{prim_id, effect}` pairs match. Without `LOCAL_RUST`, the script skips Rust execution with a message but still exits successfully.
