# tf-adapters-execution

Rust implementation of the deterministic TF-Lang execution adapter. It mirrors the TypeScript adapter and produces identical traces for the same spec fixtures.

## Usage

```rust
use std::path::Path;
use tf_adapters_execution::{load_spec, execute, write_trace};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let spec = load_spec(Path::new("spec.json"))?;
    let trace = execute(&spec)?;
    write_trace(Path::new("trace.json"), &trace)?;
    Ok(())
}
```

Errors use deterministic codes (`E_ADAPTER_*`) to align with the TS adapter. Tests ensure the JSON produced matches the TypeScript fixture byte-for-byte.

## CLI

The crate ships with a `dump` binary that mirrors the TypeScript adapter for parity testing:

```bash
cargo run --bin dump -- --spec fixtures/sample-spec.json --out trace.json
```
