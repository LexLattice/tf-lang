use anyhow::{bail, Result};
use serde_json::Value;

fn expect_int(v: &Value) -> Result<i64> {
    match v.as_i64() {
        Some(n) => Ok(n),
        None => bail!("E_L0_FLOAT"),
    }
}

fn assert_dimension_eq(args: &[Value]) -> Result<Value> {
    let a = args.get(0).ok_or_else(|| anyhow::anyhow!("arg0"))?;
    let b = args.get(1).ok_or_else(|| anyhow::anyhow!("arg1"))?;
    let a_arr = a.as_array().ok_or_else(|| anyhow::anyhow!("E_TYPE"))?;
    let b_arr = b.as_array().ok_or_else(|| anyhow::anyhow!("E_TYPE"))?;
    if a_arr.len() != b_arr.len() {
        bail!("dimension mismatch: {} != {}", a_arr.len(), b_arr.len());
    }
    Ok(Value::Bool(true))
}

fn lens_mod(args: &[Value]) -> Result<Value> {
    let x = expect_int(args.get(0).ok_or_else(|| anyhow::anyhow!("arg0"))?)?;
    let m = expect_int(args.get(1).ok_or_else(|| anyhow::anyhow!("arg1"))?)?;
    if m <= 0 {
        bail!("E_MOD_BOUNDS")
    }
    Ok(Value::from(x.rem_euclid(m)))
}

fn assert_bounds(args: &[Value]) -> Result<Value> {
    let x = expect_int(args.get(0).ok_or_else(|| anyhow::anyhow!("arg0"))?)?;
    let opts = args.get(1).unwrap_or(&Value::Null);
    let inclusive = opts.get("inclusive").and_then(Value::as_bool).unwrap_or(true);
    if let Some(min) = opts.get("min") {
        let minv = expect_int(min)?;
        if inclusive {
            if x < minv { bail!("bounds: {} < {}", x, minv); }
        } else if x <= minv { bail!("bounds: {} <= {}", x, minv); }
    }
    if let Some(max) = opts.get("max") {
        let maxv = expect_int(max)?;
        if inclusive {
            if x > maxv { bail!("bounds: {} > {}", x, maxv); }
        } else if x >= maxv { bail!("bounds: {} >= {}", x, maxv); }
    }
    Ok(Value::Bool(true))
}

fn probe_delta_bounded(args: &[Value]) -> Result<Value> {
    let seq = args.get(0).ok_or_else(|| anyhow::anyhow!("arg0"))?;
    let bound = expect_int(args.get(1).ok_or_else(|| anyhow::anyhow!("arg1"))?)?;
    let arr = seq.as_array().ok_or_else(|| anyhow::anyhow!("E_TYPE"))?;
    for (i, window) in arr.windows(2).enumerate() {
        let a = expect_int(&window[0])?;
        let b = expect_int(&window[1])?;
        let d = if a >= b {
            a.checked_sub(b).ok_or_else(|| anyhow::anyhow!("overflow"))?
        } else {
            b.checked_sub(a).ok_or_else(|| anyhow::anyhow!("overflow"))?
        };
        if d > bound { bail!("delta {} at index {}", d, i + 1); }
    }
    Ok(Value::Bool(true))
}

fn correct_saturate(args: &[Value]) -> Result<Value> {
    let x = expect_int(args.get(0).ok_or_else(|| anyhow::anyhow!("arg0"))?)?;
    let opts = args.get(1).unwrap_or(&Value::Null);
    let mut v = x;
    if let Some(min) = opts.get("min") {
        let minv = expect_int(min)?;
        v = std::cmp::max(v, minv);
    }
    if let Some(max) = opts.get("max") {
        let maxv = expect_int(max)?;
        v = std::cmp::min(v, maxv);
    }
    Ok(Value::from(v))
}

pub fn call(id: &str, args: &[Value]) -> Result<Value> {
    match id {
        "tf://assert/dimension_eq@0.1" => assert_dimension_eq(args),
        "tf://lens/mod@0.1" => lens_mod(args),
        "tf://assert/bounds@0.1" => assert_bounds(args),
        "tf://probe/delta_bounded@0.1" => probe_delta_bounded(args),
        "tf://correct/saturate@0.1" => correct_saturate(args),
        _ => Ok(Value::Null),
    }
}
