use std::{
    env,
    fs,
    path::PathBuf,
};

use anyhow::{anyhow, Context, Result};
use serde_json::Value;

use __CRATE_NAME__::{adapters::InMemoryAdapters, run_ir, DeterministicClock, TraceWriter};

const DEFAULT_IR: &str = include_str!("../../ir.json");

fn main() {
    if let Err(err) = try_main() {
        eprintln!("error: {err:?}");
        std::process::exit(1);
    }
}

fn try_main() -> Result<()> {
    let mut args = env::args().skip(1);
    let mut ir_path: Option<PathBuf> = None;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--ir" => {
                let value = args.next().context("--ir requires a value")?;
                ir_path = Some(PathBuf::from(value));
            }
            "--help" | "-h" => {
                print_help();
                return Ok(());
            }
            other => return Err(anyhow!("unexpected argument: {other}")),
        }
    }

    let ir_source = if let Some(path) = ir_path {
        fs::read_to_string(&path)
            .with_context(|| format!("reading IR from {}", path.display()))?
    } else {
        DEFAULT_IR.to_string()
    };

    let ir: Value = serde_json::from_str(&ir_source).context("parsing IR JSON")?;
    let mut adapters = InMemoryAdapters::new();
    let mut clock = DeterministicClock::new();
    let mut trace = TraceWriter::new()?;
    run_ir(&ir, &mut adapters, &mut trace, &mut clock)?;
    trace.finalize()?;
    Ok(())
}

fn print_help() {
    eprintln!("Usage: run --ir <path>");
}
