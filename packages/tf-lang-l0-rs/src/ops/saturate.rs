use anyhow::{bail, Result};
use serde_json::Value;

pub fn saturate(v: &Value, opts: &Value) -> Result<Value> {
    let n = v.as_i64().ok_or_else(|| anyhow::anyhow!("E_SAT_TYPE"))?;
    let min = opts.get("min").and_then(|x| x.as_i64()).ok_or_else(|| anyhow::anyhow!("E_SAT_TYPE"))?;
    let max = opts.get("max").and_then(|x| x.as_i64()).ok_or_else(|| anyhow::anyhow!("E_SAT_TYPE"))?;
    if min > max {
        bail!("E_SAT_BOUNDS");
    }
    let clamped = if n < min {
        min
    } else if n > max {
        max
    } else {
        n
    };
    Ok(Value::Number(clamped.into()))
}
