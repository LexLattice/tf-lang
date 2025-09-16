# tf-adapters-execution

Rust implementation of the deterministic TF-Lang execution adapter. It mirrors the TypeScript adapter and produces identical traces for the same spec fixtures.

## Usage

```rust
use clap::Parser;
use std::path::PathBuf;
use tf_adapters_execution::{execute, load_spec, write_trace};

#[derive(Parser, Debug)]
#[command(name = "dump", about = "Execute spec and write a canonical trace")]
struct Args {
    /// Input spec path (JSON)
    #[arg(short, long)]
    spec: PathBuf,
    /// Output trace path (JSON)
    #[arg(short, long)]
    out: PathBuf,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();
    let spec = load_spec(&args.spec)?;
    let trace = execute(&spec)?;
    write_trace(&args.out, &trace)?;
    Ok(())
}
```

Errors use deterministic codes (`E_ADAPTER_*`) to align with the TS adapter. Tests ensure the JSON produced matches the TypeScript fixture byte-for-byte.
