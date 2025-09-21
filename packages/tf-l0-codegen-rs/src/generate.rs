use std::env;
use std::fs::File;
use std::path::PathBuf;

use anyhow::{Context, Result};
use tf_l0_codegen_rs::{emit_workspace, Node};

fn main() -> Result<()> {
    let args = Arguments::parse()?;
    let file = File::open(&args.ir)
        .with_context(|| format!("unable to open IR at {}", args.ir.display()))?;
    let ir: Node = serde_json::from_reader(file).context("failed to parse IR JSON")?;
    emit_workspace(&ir, &args.out_dir)
}

struct Arguments {
    ir: PathBuf,
    out_dir: PathBuf,
}

impl Arguments {
    fn parse() -> Result<Self> {
        let mut args = env::args().skip(1);
        let mut ir = None;
        let mut out_dir = None;

        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--ir" => {
                    let value = args.next().context("expected a value for --ir")?;
                    ir = Some(PathBuf::from(value));
                }
                "--out" | "--out-dir" => {
                    let value = args.next().context("expected a value for --out")?;
                    out_dir = Some(PathBuf::from(value));
                }
                other => {
                    anyhow::bail!("unknown argument: {}", other);
                }
            }
        }

        let ir = ir.context("missing --ir <path>")?;
        let out_dir = out_dir.context("missing --out <dir>")?;

        Ok(Self { ir, out_dir })
    }
}
