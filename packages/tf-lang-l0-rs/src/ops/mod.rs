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
    if !a.is_array() || !b.is_array() {
        bail!("E_TYPE")
    }
    if a.as_array().unwrap().len() != b.as_array().unwrap().len() {
        bail!("dimension mismatch: {} != {}", a.as_array().unwrap().len(), b.as_array().unwrap().len());
    }
    Ok(Value::Bool(true))
}

fn lens_mod(args: &[Value]) -> Result<Value> {
    let x = expect_int(args.get(0).ok_or_else(|| anyhow::anyhow!("arg0"))?)?;
    let m = expect_int(args.get(1).ok_or_else(|| anyhow::anyhow!("arg1"))?)?;
    if m <= 0 {
        bail!("E_MOD_BOUNDS")
    }
    let mut r = x % m;
    if r < 0 {
        r += m;
    }
    Ok(Value::from(r))
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
    for i in 1..arr.len() {
        let a = expect_int(&arr[i - 1])?;
        let b = expect_int(&arr[i])?;
        let d = (a - b).abs();
        if d > bound { bail!("delta {} at index {}", d, i); }
    }
    Ok(Value::Bool(true))
}

fn correct_saturate(args: &[Value]) -> Result<Value> {
    let x = expect_int(args.get(0).ok_or_else(|| anyhow::anyhow!("arg0"))?)?;
    let opts = args.get(1).unwrap_or(&Value::Null);
    let mut v = x;
    if let Some(min) = opts.get("min") {
        let minv = expect_int(min)?;
        if v < minv { v = minv; }
    }
    if let Some(max) = opts.get("max") {
        let maxv = expect_int(max)?;
        if v > maxv { v = maxv; }
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
