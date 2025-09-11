use anyhow::{bail, Result};
use serde_json::Value;

pub fn dimension_eq(a: &Value, b: &Value) -> Result<Value> {
    match (a, b) {
        (Value::Array(aa), Value::Array(bb)) => {
            if aa.len() == bb.len() {
                Ok(Value::Bool(true))
            } else {
                bail!("dimension mismatch: {} vs {}", aa.len(), bb.len());
            }
        }
        _ => bail!("dimension_eq expects arrays"),
    }
}
