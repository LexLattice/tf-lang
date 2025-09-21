use std::env;
use std::fs::{self, File};
use std::io::{self, BufWriter, Write};
use std::path::PathBuf;

use anyhow::{anyhow, Context, Result};
use serde_json::Value;

use {{crate_name}}::{run_pipeline, InMemoryAdapters};

const BAKED_IR: &str = include_str!("../ir.json");

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
                print_usage();
                return Ok(());
            }
            other => return Err(anyhow!("unexpected argument: {other}")),
        }
    }

    let ir_source = if let Some(path) = ir_path {
        fs::read_to_string(&path).with_context(|| format!("reading IR from {path:?}"))?
    } else {
        BAKED_IR.to_string()
    };

    let ir: Value = serde_json::from_str(&ir_source).context("parsing IR JSON")?;
    let mut adapters = InMemoryAdapters::default();
    let trace = run_pipeline(&ir, &mut adapters)?;

    let out_dir = PathBuf::from("out");
    fs::create_dir_all(&out_dir).context("creating out directory")?;
    let trace_path = out_dir.join("trace.jsonl");
    let file = File::create(&trace_path).context("creating trace.jsonl")?;
    let mut file_writer = BufWriter::new(file);
    let stdout = io::stdout();
    let mut stdout_writer = BufWriter::new(stdout);

    for entry in trace {
        let line = serde_json::to_string(&entry.to_json_value()).context("serializing trace entry")?;
        writeln!(file_writer, "{line}").context("writing trace file")?;
        writeln!(stdout_writer, "{line}").context("writing trace stdout")?;
    }

    file_writer.flush().context("flushing trace file")?;
    stdout_writer.flush().context("flushing stdout")?;
    Ok(())
}

fn print_usage() {
    eprintln!("Usage: run [--ir <path>]");
}
