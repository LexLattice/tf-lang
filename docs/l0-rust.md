# L0 Rust backend

This repo can emit a runnable Rust crate for an L0 IR. Generation is deterministic and works without requiring a local Rust toolchain. Running the binary is optional and only needed when you want to compare traces locally.

## Generating a crate

```bash
node scripts/generate-rs-run.mjs out/0.4/ir/signing.ir.json -o out/0.4/codegen-rs/signing
```

The command writes a Cargo workspace under the requested output directory. By default it skips executing the compiled binary.

## Running the crate (optional)

Set `LOCAL_RUST=1` to enable the cargo run step. The helper respects `RUST_TRACE_PATH` if you want to override the trace location; otherwise it writes to `<crate>/out/trace.jsonl`.

```bash
LOCAL_RUST=1 cargo run --manifest-path out/0.4/codegen-rs/signing/Cargo.toml -- --ir out/0.4/ir/signing.ir.json
```

The binary reads the baked IR (or the `--ir` override) and emits trace records conforming to `trace.v0.4` (without provenance metadata).
