# L0 Rust runner quickstart

The generated Rust crates mirror the TypeScript runtime with in-memory adapters and a `run` binary that emits trace.v0.4 JSONL. Generation does not require a Rust toolchain; executing the binary is opt-in via `LOCAL_RUST=1`.

```bash
# Generate the crate for an existing IR (no cargo toolchain required)
node scripts/generate-rs-run.mjs out/0.4/ir/signing.ir.json -o out/0.4/codegen-rs/signing

# Optionally run the crate locally to produce out/trace.jsonl
LOCAL_RUST=1 cargo run --manifest-path out/0.4/codegen-rs/signing/Cargo.toml -- --ir out/0.4/ir/signing.ir.json
```

The binary respects `TF_TRACE_PATH`; when unset it writes to `out/trace.jsonl` within the crate directory.
