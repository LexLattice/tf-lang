use serde_json::Value;

pub fn delta_bounded(arr: &Value, bound: &Value) -> bool {
    let b = match bound.as_i64() {
        Some(v) if v >= 0 => v,
        _ => return false,
    };
    let list = match arr.as_array() {
        Some(v) => v,
        None => return false,
    };
    for i in 1..list.len() {
        let a = match list[i - 1].as_i64() {
            Some(v) => v,
            None => return false,
        };
        let c = match list[i].as_i64() {
            Some(v) => v,
            None => return false,
        };
        if (c - a).abs() > b {
            return false;
        }
    }
    true
}
