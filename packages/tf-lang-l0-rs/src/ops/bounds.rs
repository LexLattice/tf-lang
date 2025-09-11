use anyhow::{bail, Result};
use serde_json::Value;

pub fn assert_bounds(v: &Value, opts: &Value) -> Result<Value> {
    let n = v.as_i64().ok_or_else(|| anyhow::anyhow!("E_BOUNDS_TYPE"))?;
    let min = opts.get("min").and_then(|x| x.as_i64()).unwrap_or(i64::MIN);
    let max = opts.get("max").and_then(|x| x.as_i64()).unwrap_or(i64::MAX);
    let inclusive = opts.get("inclusive").and_then(|x| x.as_bool()).unwrap_or(true);
    if inclusive {
        if n < min || n > max {
            bail!("E_BOUNDS:{}", n);
        }
    } else {
        if n <= min || n >= max {
            bail!("E_BOUNDS:{}", n);
        }
    }
    Ok(Value::Null)
}
