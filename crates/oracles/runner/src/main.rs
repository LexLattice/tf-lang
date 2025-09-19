use std::fs;
use std::path::PathBuf;

use clap::{Parser, ValueEnum};
use serde::Serialize;
use tf_oracles_conservation::{check_conservation, ConservationInput};
use tf_oracles_core::{canonical_string, OracleCtx};
use tf_oracles_idempotence::{check_idempotence, IdempotenceInput};
use tf_oracles_transport::{check_transport, TransportInput};
use thiserror::Error;

#[derive(Parser)]
#[command(author, version, about = "Run TF-Lang oracles from the CLI.")]
struct Args {
    #[arg(long, value_enum)]
    oracle: OracleKind,

    #[arg(long)]
    input: PathBuf,

    #[arg(long, default_value = "0xfeed")]
    seed: String,

    #[arg(long, default_value_t = 0)]
    now: i64,
}

#[derive(Copy, Clone, Debug, ValueEnum)]
enum OracleKind {
    Conservation,
    Idempotence,
    Transport,
}

#[derive(Debug, Error)]
enum RunnerError {
    #[error("failed to read input: {0}")]
    Read(#[from] std::io::Error),
    #[error("failed to parse input JSON: {0}")]
    Parse(#[from] serde_json::Error),
    #[error("failed to serialize result: {0}")]
    Serialize(#[from] tf_oracles_core::CanonError),
}

fn main() {
    let args = Args::parse();
    if let Err(error) = run(args) {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run(args: Args) -> Result<(), RunnerError> {
    let payload = fs::read_to_string(&args.input)?;
    let ctx = OracleCtx::new(args.seed).with_now(args.now);

    match args.oracle {
        OracleKind::Conservation => {
            let input: ConservationInput = serde_json::from_str(&payload)?;
            emit(check_conservation(&input, &ctx))?
        }
        OracleKind::Idempotence => {
            let input: IdempotenceInput = serde_json::from_str(&payload)?;
            emit(check_idempotence(&input, &ctx))?
        }
        OracleKind::Transport => {
            let input: TransportInput = serde_json::from_str(&payload)?;
            emit(check_transport(&input, &ctx))?
        }
    }

    Ok(())
}

fn emit<T>(result: T) -> Result<(), RunnerError>
where
    T: Serialize,
{
    let serialized = canonical_string(&result)?;
    println!("{}", serialized);
    Ok(())
}
