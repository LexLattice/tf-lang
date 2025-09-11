use anyhow::{bail, Result};
use serde_json::Value;

pub fn dimension_eq(a: &Value, b: &Value) -> Result<Value> {
    if !a.is_array() || !b.is_array() {
        bail!("E_DIMENSION_TYPE");
    }
    if a.as_array().unwrap().len() != b.as_array().unwrap().len() {
        bail!("E_DIMENSION_MISMATCH");
    }
    Ok(Value::Null)
}
