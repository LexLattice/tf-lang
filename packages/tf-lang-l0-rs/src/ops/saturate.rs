use anyhow::{anyhow, bail, Result};
use serde_json::{json, Value};

pub fn saturate(x: &Value, min: &Value, max: &Value, field: &Value) -> Result<Value> {
    let xi = x.as_i64().ok_or_else(|| anyhow!("x must be integer"))?;
    let minv = min.as_i64().ok_or_else(|| anyhow!("min must be integer"))?;
    let maxv = max.as_i64().ok_or_else(|| anyhow!("max must be integer"))?;
    if minv > maxv {
        bail!("min greater than max");
    }
    let mut r = xi;
    if r < minv {
        r = minv;
    }
    if r > maxv {
        r = maxv;
    }
    let note = if r == xi {
        Value::Null
    } else {
        json!({
            "field": field.clone(),
            "before": xi,
            "after": r,
            "reason": "saturate"
        })
    };
    Ok(json!({ "tag": "sat", "values": [r, note] }))
}
