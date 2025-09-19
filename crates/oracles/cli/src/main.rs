use std::env;
use std::error::Error;
use std::fs;

use serde::Serialize;
use serde_json::Value;
use tf_oracles_conservation::{check_conservation, ConservationInput};
use tf_oracles_core::{canonicalize_value, OracleCtx, OracleResult};
use tf_oracles_idempotence::{check_idempotence, IdempotenceInput};
use tf_oracles_transport::{check_transport, TransportInput};

fn main() {
    if let Err(error) = run() {
        eprintln!("error: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let args = Args::parse()?;
    let input_text = fs::read_to_string(&args.input_path)?;
    let json_value: Value = serde_json::from_str(&input_text)?;
    let ctx = OracleCtx::new("0xfeed").with_now(0);
    let payload = json_value
        .get("input")
        .cloned()
        .unwrap_or_else(|| json_value.clone());

    match args.oracle.as_str() {
        "conservation" => {
            let input: ConservationInput = serde_json::from_value(payload.clone())?;
            let result = check_conservation(&input, &ctx);
            print_result(&result)?;
        }
        "idempotence" => {
            let input: IdempotenceInput = serde_json::from_value(payload.clone())?;
            let result = check_idempotence(&input, &ctx);
            print_result(&result)?;
        }
        "transport" => {
            let input: TransportInput = serde_json::from_value(payload)?;
            let result = check_transport(&input, &ctx);
            print_result(&result)?;
        }
        other => {
            return Err(format!("unknown oracle: {other}").into());
        }
    }

    Ok(())
}

fn print_result<T>(result: &OracleResult<T>) -> Result<(), Box<dyn Error>>
where
    T: Serialize,
{
    let value = serde_json::to_value(result)?;
    let canonical = canonicalize_value(value);
    println!("{}", serde_json::to_string(&canonical)?);
    Ok(())
}

struct Args {
    oracle: String,
    input_path: String,
}

impl Args {
    fn parse() -> Result<Self, Box<dyn Error>> {
        let mut oracle: Option<String> = None;
        let mut input: Option<String> = None;
        let mut iter = env::args().skip(1);
        while let Some(flag) = iter.next() {
            match flag.as_str() {
                "--oracle" => {
                    let value = iter.next().ok_or("missing value for --oracle")?;
                    oracle = Some(value);
                }
                "--input" => {
                    let value = iter.next().ok_or("missing value for --input")?;
                    input = Some(value);
                }
                other => {
                    return Err(format!("unknown argument: {other}").into());
                }
            }
        }

        let oracle = oracle.ok_or("--oracle is required")?;
        let input_path = input.ok_or("--input is required")?;
        Ok(Self { oracle, input_path })
    }
}
