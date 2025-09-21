use std::{
    env,
    io::{self, Read},
    path::PathBuf,
};

use anyhow::{anyhow, Context, Result};
use serde_json::Value;
use tf_l0_codegen_rs::generate_workspace;

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {err:?}");
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    let mut args = env::args().skip(1);
    let mut out_dir: Option<PathBuf> = None;
    let mut package_name: Option<String> = None;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--out-dir" => {
                let value = args.next().context("--out-dir requires a value")?;
                out_dir = Some(PathBuf::from(value));
            }
            "--package-name" => {
                let value = args.next().context("--package-name requires a value")?;
                package_name = Some(value);
            }
            "--help" | "-h" => {
                print_usage();
                return Ok(());
            }
            other => return Err(anyhow!("unexpected argument: {other}")),
        }
    }

    let out_dir = out_dir.context("missing --out-dir")?;
    let package_name = package_name.unwrap_or_else(|| "tf_generated".to_string());

    let mut buffer = String::new();
    io::stdin()
        .read_to_string(&mut buffer)
        .context("reading IR from stdin")?;

    if buffer.trim().is_empty() {
        return Err(anyhow!("expected IR JSON on stdin"));
    }

    let ir: Value = serde_json::from_str(&buffer).context("parsing IR JSON")?;
    generate_workspace(&ir, &out_dir, &package_name)
}

fn print_usage() {
    eprintln!("Usage: generate --out-dir <path> [--package-name <name>] < ir.json");
}
