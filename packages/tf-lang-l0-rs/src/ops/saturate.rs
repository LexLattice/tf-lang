use anyhow::{anyhow, bail, Result};
use serde_json::Value;

pub fn saturate(x: &Value, opts: &Value) -> Result<Value> {
    let xi = x.as_i64().ok_or_else(|| anyhow!("E_L0_TYPE"))?;
    let min = opts.get("min").and_then(|v| v.as_i64()).ok_or_else(|| anyhow!("E_L0_TYPE"))?;
    let max = opts.get("max").and_then(|v| v.as_i64()).ok_or_else(|| anyhow!("E_L0_TYPE"))?;
    if min > max {
        bail!("E_L0_BOUNDS");
    }
    let mut out = xi;
    if xi < min {
        out = min;
    }
    if xi > max {
        out = max;
    }
    Ok(Value::Number(out.into()))
}
