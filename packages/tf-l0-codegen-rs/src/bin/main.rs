use std::env;
use std::path::PathBuf;

use anyhow::{anyhow, Result};
use tf_l0_codegen_rs::generate_from_ir_path;

fn main() -> Result<()> {
    let mut args = env::args().skip(1);
    let mut ir_path: Option<PathBuf> = None;
    let mut out_dir: Option<PathBuf> = None;
    let mut name: Option<String> = None;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--ir" => {
                let next = args
                    .next()
                    .ok_or_else(|| anyhow!("expected value after --ir"))?;
                ir_path = Some(PathBuf::from(next));
            }
            "--out" | "-o" => {
                let next = args
                    .next()
                    .ok_or_else(|| anyhow!("expected value after --out"))?;
                out_dir = Some(PathBuf::from(next));
            }
            "--name" | "--package" => {
                let next = args
                    .next()
                    .ok_or_else(|| anyhow!("expected value after --name"))?;
                name = Some(next);
            }
            value if !value.starts_with('-') && ir_path.is_none() => {
                ir_path = Some(PathBuf::from(value));
            }
            other => {
                return Err(anyhow!("unrecognized argument `{}`", other));
            }
        }
    }

    let ir_path = ir_path.ok_or_else(|| anyhow!("missing --ir argument"))?;
    let out_dir = out_dir.ok_or_else(|| anyhow!("missing --out argument"))?;
    let package_name = generate_from_ir_path(&ir_path, &out_dir, name.as_deref())?;
    println!(
        "Generated crate `{}` at {}",
        package_name,
        out_dir.display()
    );
    Ok(())
}
