use serde_json::Value;

pub fn dimension_eq(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Array(x), Value::Array(y)) => x.len() == y.len(),
        _ => false,
    }
}
