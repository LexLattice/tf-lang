use anyhow::Result;
use serde_json::Value;

pub fn lens_mod(x: &Value, m: &Value) -> Result<Value> {
    let xi = match x.as_i64() {
        Some(v) => v,
        None => return Ok(Value::Null),
    };
    let mi = match m.as_i64() {
        Some(v) => v,
        None => return Ok(Value::Null),
    };
    if mi <= 0 {
        return Ok(Value::Null);
    }
    let r = ((xi % mi) + mi) % mi;
    Ok(Value::Number(r.into()))
}
