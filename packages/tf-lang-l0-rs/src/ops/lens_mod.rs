use anyhow::{anyhow, bail, Result};
use serde_json::Value;

pub fn lens_mod(x: &Value, m: &Value) -> Result<Value> {
    let xi = x.as_i64().ok_or_else(|| anyhow!("x must be integer"))?;
    let mi = m.as_i64().ok_or_else(|| anyhow!("mod must be integer"))?;
    if mi <= 0 {
        bail!("mod must be >0");
    }
    let mut r = xi % mi;
    if r < 0 {
        r += mi;
    }
    Ok(Value::Number(r.into()))
}
