use anyhow::{bail, Result};
use serde_json::Value;

pub fn delta_bounded(seq: &Value, bound: &Value) -> Result<Value> {
    let arr = seq.as_array().ok_or_else(|| anyhow::anyhow!("E_DELTA_TYPE"))?;
    let b = bound.as_i64().ok_or_else(|| anyhow::anyhow!("E_DELTA_TYPE"))?;
    if b < 0 {
        bail!("E_DELTA_BOUNDS");
    }
    let mut prev: Option<i64> = None;
    for (i, v) in arr.iter().enumerate() {
        let n = v.as_i64().ok_or_else(|| anyhow::anyhow!("E_L0_FLOAT"))?;
        if let Some(p) = prev {
            let d = (n - p).abs();
            if d > b {
                bail!("E_DELTA_BOUNDS:{}:{}", i, d);
            }
        }
        prev = Some(n);
    }
    Ok(Value::Null)
}
