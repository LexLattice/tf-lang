use serde_json::Value;

pub fn bounds(x: &Value, opts: &Value) -> bool {
    let xi = match x.as_i64() {
        Some(v) => v,
        None => return false,
    };
    if let Some(min) = opts.get("min").and_then(|v| v.as_i64()) {
        if xi < min {
            return false;
        }
    }
    if let Some(max) = opts.get("max").and_then(|v| v.as_i64()) {
        if xi > max {
            return false;
        }
    }
    true
}
