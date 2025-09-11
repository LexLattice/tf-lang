use anyhow::{anyhow, bail, Result};
use serde_json::Value;

pub fn bounds(x: &Value, opts: &Value) -> Result<Value> {
    let xi = x.as_i64().ok_or_else(|| anyhow!("x must be integer"))?;
    let min = if let Some(v) = opts.get("min") {
        Some(v.as_i64().ok_or_else(|| anyhow!("min must be integer"))?)
    } else {
        None
    };
    let max = if let Some(v) = opts.get("max") {
        Some(v.as_i64().ok_or_else(|| anyhow!("max must be integer"))?)
    } else {
        None
    };
    let inclusive = opts
        .get("inclusive")
        .and_then(|v| v.as_bool())
        .unwrap_or(true);
    if let Some(m) = min {
        if (inclusive && xi < m) || (!inclusive && xi <= m) {
            bail!("min bound {} violated by {}", m, xi);
        }
    }
    if let Some(m) = max {
        if (inclusive && xi > m) || (!inclusive && xi >= m) {
            bail!("max bound {} violated by {}", m, xi);
        }
    }
    Ok(Value::Bool(true))
}
