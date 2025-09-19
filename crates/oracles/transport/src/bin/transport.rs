use std::env;
use std::fs;
use std::io::{self, Read};

use serde::Deserialize;
use serde_json;
use tf_oracles_core::{OracleCtx, OracleResult};
use tf_oracles_transport::{check_transport, TransportInput, TransportReport};

#[derive(Deserialize)]
struct Request {
    input: TransportInput,
    ctx: OracleCtx,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut buffer = String::new();
    if let Some(path) = env::args().nth(1) {
        buffer = fs::read_to_string(path)?;
    } else {
        io::stdin().read_to_string(&mut buffer)?;
    }
    let request: Request = serde_json::from_str(&buffer)?;
    let result: OracleResult<TransportReport> = check_transport(&request.input, &request.ctx);
    serde_json::to_writer(io::stdout(), &result)?;
    Ok(())
}
