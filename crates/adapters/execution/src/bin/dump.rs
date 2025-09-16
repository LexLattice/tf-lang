use std::env;
use std::path::PathBuf;

use tf_adapters_execution::{execute, load_spec, write_trace};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: dump <spec> <out>");
        std::process::exit(1);
    }
    let spec_path = PathBuf::from(&args[1]);
    let out_path = PathBuf::from(&args[2]);
    let spec = load_spec(&spec_path)?;
    let trace = execute(&spec)?;
    write_trace(&out_path, &trace)?;
    Ok(())
}
