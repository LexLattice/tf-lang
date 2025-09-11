use anyhow::{anyhow, bail, Result};
use serde_json::{json, Value};

pub fn delta_bounded(seq: &Value, bound: &Value) -> Result<Value> {
    let arr = seq.as_array().ok_or_else(|| anyhow!("delta_bounded expects array"))?;
    let b = bound.as_i64().ok_or_else(|| anyhow!("bound must be integer"))?;
    if b < 0 {
        bail!("bound must be non-negative");
    }
    for i in 1..arr.len() {
        let prev = arr[i - 1].as_i64().ok_or_else(|| anyhow!("seq must contain integers"))?;
        let cur = arr[i].as_i64().ok_or_else(|| anyhow!("seq must contain integers"))?;
        let diff = cur - prev;
        if diff.abs() > b {
            return Ok(json!({ "index": i, "delta": diff }));
        }
    }
    Ok(Value::Bool(true))
}
