# L0 Rust code generation

This repository includes an experimental Rust code generator that mirrors the TypeScript in-memory runtime. The generated crates contain deterministic in-memory adapters, a reusable IR runner, and a `run` binary that can execute an IR file and emit trace lines compatible with `trace.v0.4`.

## Generating a Rust crate

```bash
node scripts/generate-rs-run.mjs out/0.4/ir/signing.ir.json -o out/0.4/codegen-rs/signing
```

The command copies the IR into the crate, writes deterministic sources under `src/`, and produces a `Cargo.toml` with the required dependencies. Re-running the generator overwrites files with identical content, making regeneration safe.

## Running the generated binary locally

When a Rust toolchain is available, set `LOCAL_RUST=1` to build and run the crate immediately. The helper script forwards the IR path and captures the emitted trace under the crate's `out/` directory.

```bash
LOCAL_RUST=1 cargo run --manifest-path out/0.4/codegen-rs/signing/Cargo.toml -- --ir out/0.4/ir/signing.ir.json
```

The binary honours `TF_TRACE_PATH`; by default the helper script points it at `out/trace.jsonl` inside the crate. Each invocation appends JSONL entries mirroring the TypeScript runtime, modulo timestamp differences.
