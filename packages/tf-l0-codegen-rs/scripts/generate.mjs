import { writeFile, mkdir } from 'node:fs/promises';
import { join } from 'node:path';

export async function generate(ir, { outDir }) {
  await mkdir(join(outDir, 'src'), { recursive: true });
  await writeFile(join(outDir, 'Cargo.toml'), `[package]
name = "tf_generated"
version = "0.1.0"
edition = "2021"

[dependencies]
serde = { version = "1", features=["derive"] }
serde_json = "1"
anyhow = "1"
tokio = { version = "1", features = ["full"] }
`, 'utf8');

  await writeFile(join(outDir, 'src', 'lib.rs'), `use anyhow::Result;
use serde_json::Value;

pub async fn run(adapters: &Adapters, input: Value) -> Result<Value> {
    step_${hash(ir)}(adapters, input).await
}

pub trait Adapters {
    // Fill with methods for primitives
}

async fn step_${hash(ir)}(_adapters: &Adapters, input: Value) -> Result<Value> {
    Ok(input)
}
`, 'utf8');
}

function hash(value){ const s = JSON.stringify(value); let h=0; for(let i=0;i<s.length;i++){ h=((h<<5)-h)+s.charCodeAt(i)|0; } return Math.abs(h); }
