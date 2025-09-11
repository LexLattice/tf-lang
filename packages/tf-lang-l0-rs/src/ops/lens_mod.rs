use anyhow::{bail, Result};
use serde_json::Value;

pub fn lens_mod(x: &Value, m: &Value) -> Result<Value> {
    let xi = x.as_i64().ok_or_else(|| anyhow::anyhow!("E_MOD_TYPE"))?;
    let mi = m.as_i64().ok_or_else(|| anyhow::anyhow!("E_MOD_TYPE"))?;
    if mi <= 0 {
        bail!("E_MOD_BOUNDS");
    }
    let r = ((xi % mi) + mi) % mi;
    Ok(Value::Number(r.into()))
}
