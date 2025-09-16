use std::path::PathBuf;

use clap::Parser;
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
