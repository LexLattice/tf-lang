# L0 Rust runtime quickstart

## Generate Rust code for an IR

```bash
node scripts/generate-rs-run.mjs out/0.4/ir/signing.ir.json -o out/0.4/codegen-rs/signing
```

This writes a standalone crate with in-memory adapters, a baked IR snapshot, and a `run` binary.

## Execute the generated runner (local Rust only)

```bash
LOCAL_RUST=1 cargo run --manifest-path out/0.4/codegen-rs/signing/Cargo.toml -- --ir out/0.4/ir/signing.ir.json
```

The runner prints JSONL trace lines to stdout and mirrors them to `out/trace.jsonl` inside the crate directory.

## Cross-runtime parity

```bash
node scripts/cross-parity-ts-rs.mjs examples/flows/run_publish.tf
```

When `LOCAL_RUST=1` is set, this script runs both TS and Rust runners and records their trace comparison at `out/0.4/parity/ts-rs/report.json`.
