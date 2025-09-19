use serde::{Deserialize, Serialize};
use serde_json::Value;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct DiffResult {
    pub pointer: String,
    pub left: Value,
    pub right: Value,
}

pub fn diff_values(left: &Value, right: &Value, missing_value: &Value) -> Option<DiffResult> {
    diff_values_inner(left, right, missing_value, &mut Vec::new())
}

fn diff_values_inner(
    left: &Value,
    right: &Value,
    missing_value: &Value,
    segments: &mut Vec<String>,
) -> Option<DiffResult> {
    if left == right {
        return None;
    }

    match (left, right) {
        (Value::Array(left_items), Value::Array(right_items)) => {
            let max = left_items.len().min(right_items.len());
            for index in 0..max {
                segments.push(index.to_string());
                let child = diff_values_inner(
                    &left_items[index],
                    &right_items[index],
                    missing_value,
                    segments,
                );
                segments.pop();
                if child.is_some() {
                    return child;
                }
            }

            if left_items.len() != right_items.len() {
                let pointer = pointer_from_segments_with_extra(
                    segments,
                    &left_items,
                    &right_items,
                    missing_value,
                );
                return Some(pointer);
            }

            None
        }
        (Value::Array(_), _) | (_, Value::Array(_)) => {
            Some(build_result(left.clone(), right.clone(), segments))
        }
        (Value::Object(left_map), Value::Object(right_map)) => {
            let mut keys = left_map.keys().cloned().collect::<Vec<_>>();
            for key in right_map.keys() {
                if !left_map.contains_key(key) {
                    keys.push(key.clone());
                }
            }
            keys.sort();
            keys.dedup();

            for key in keys {
                let has_left = left_map.contains_key(&key);
                let has_right = right_map.contains_key(&key);
                segments.push(key.clone());
                if !has_left || !has_right {
                    let left_value = left_map
                        .get(&key)
                        .cloned()
                        .unwrap_or_else(|| missing_value.clone());
                    let right_value = right_map
                        .get(&key)
                        .cloned()
                        .unwrap_or_else(|| missing_value.clone());
                    let pointer = pointer_from_segments(segments);
                    segments.pop();
                    return Some(DiffResult {
                        pointer,
                        left: left_value,
                        right: right_value,
                    });
                }

                let child = diff_values_inner(
                    left_map.get(&key).unwrap(),
                    right_map.get(&key).unwrap(),
                    missing_value,
                    segments,
                );
                segments.pop();
                if child.is_some() {
                    return child;
                }
            }

            None
        }
        (Value::Object(_), _) | (_, Value::Object(_)) => {
            Some(build_result(left.clone(), right.clone(), segments))
        }
        _ => Some(build_result(left.clone(), right.clone(), segments)),
    }
}

fn pointer_from_segments_with_extra(
    segments: &mut Vec<String>,
    left_items: &[Value],
    right_items: &[Value],
    missing_value: &Value,
) -> DiffResult {
    let index = left_items.len().min(right_items.len());
    segments.push(index.to_string());
    let pointer = pointer_from_segments(segments);
    segments.pop();

    let left_value = if index < left_items.len() {
        left_items[index].clone()
    } else {
        missing_value.clone()
    };
    let right_value = if index < right_items.len() {
        right_items[index].clone()
    } else {
        missing_value.clone()
    };

    DiffResult {
        pointer,
        left: left_value,
        right: right_value,
    }
}

fn build_result(left: Value, right: Value, segments: &mut Vec<String>) -> DiffResult {
    DiffResult {
        pointer: pointer_from_segments(segments),
        left,
        right,
    }
}

pub fn pointer_from_segments(segments: &[String]) -> String {
    if segments.is_empty() {
        return String::new();
    }

    let mut pointer = String::new();
    for segment in segments {
        pointer.push('/');
        pointer.push_str(&escape_pointer_segment(segment));
    }
    pointer
}

pub fn escape_pointer_segment(segment: &str) -> String {
    segment.replace('~', "~0").replace('/', "~1")
}
