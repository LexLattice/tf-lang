use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use serde_json::Value;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct DiffEntry {
    pub pointer: String,
    pub left: Value,
    pub right: Value,
}

#[derive(Debug, Clone, Copy, Default)]
pub struct DiffOptions<'a> {
    pub missing_value: Option<&'a Value>,
}

pub fn diff_canonical(left: &Value, right: &Value, options: DiffOptions<'_>) -> Option<DiffEntry> {
    diff_internal(left, right, Vec::new(), &options)
}

fn diff_internal(
    left: &Value,
    right: &Value,
    segments: Vec<String>,
    options: &DiffOptions<'_>,
) -> Option<DiffEntry> {
    if left == right {
        return None;
    }

    match (left, right) {
        (Value::Array(left_entries), Value::Array(right_entries)) => {
            let shared_length = left_entries.len().min(right_entries.len());
            for index in 0..shared_length {
                let mut child_segments = segments.clone();
                child_segments.push(index.to_string());
                if let Some(diff) = diff_internal(
                    &left_entries[index],
                    &right_entries[index],
                    child_segments,
                    options,
                ) {
                    return Some(diff);
                }
            }

            if left_entries.len() != right_entries.len() {
                let mut pointer_segments = segments.clone();
                pointer_segments.push(shared_length.to_string());
                let pointer = pointer_from_segments(&pointer_segments);
                if left_entries.len() > right_entries.len() {
                    let left_value = left_entries
                        .get(shared_length)
                        .cloned()
                        .unwrap_or(Value::Null);
                    return Some(DiffEntry {
                        pointer,
                        left: left_value,
                        right: clone_missing(options),
                    });
                }
                let right_value = right_entries
                    .get(shared_length)
                    .cloned()
                    .unwrap_or(Value::Null);
                return Some(DiffEntry {
                    pointer,
                    left: clone_missing(options),
                    right: right_value,
                });
            }
        }
        (Value::Object(left_map), Value::Object(right_map)) => {
            let mut keys = BTreeSet::new();
            keys.extend(left_map.keys().cloned());
            keys.extend(right_map.keys().cloned());

            for key in keys {
                let mut child_segments = segments.clone();
                child_segments.push(key.clone());
                let left_value = left_map.get(&key);
                let right_value = right_map.get(&key);

                match (left_value, right_value) {
                    (Some(left_inner), Some(right_inner)) => {
                        if let Some(diff) =
                            diff_internal(left_inner, right_inner, child_segments, options)
                        {
                            return Some(diff);
                        }
                    }
                    (Some(left_inner), None) => {
                        return Some(DiffEntry {
                            pointer: pointer_from_segments(&child_segments),
                            left: left_inner.clone(),
                            right: clone_missing(options),
                        });
                    }
                    (None, Some(right_inner)) => {
                        return Some(DiffEntry {
                            pointer: pointer_from_segments(&child_segments),
                            left: clone_missing(options),
                            right: right_inner.clone(),
                        });
                    }
                    (None, None) => continue,
                }
            }
        }
        _ => {
            let pointer = pointer_from_segments(&segments);
            return Some(DiffEntry {
                pointer,
                left: left.clone(),
                right: right.clone(),
            });
        }
    }

    if !matches!(
        (left, right),
        (Value::Array(_), Value::Array(_)) | (Value::Object(_), Value::Object(_))
    ) {
        let pointer = pointer_from_segments(&segments);
        return Some(DiffEntry {
            pointer,
            left: left.clone(),
            right: right.clone(),
        });
    }

    None
}

fn clone_missing(options: &DiffOptions<'_>) -> Value {
    options
        .missing_value
        .map(|value| value.clone())
        .unwrap_or(Value::Null)
}

pub fn pointer_from_segments<S>(segments: &[S]) -> String
where
    S: AsRef<str>,
{
    if segments.is_empty() {
        return String::new();
    }
    let escaped: Vec<String> = segments
        .iter()
        .map(|segment| escape_pointer_segment(segment.as_ref()))
        .collect();
    format!("/{}", escaped.join("/"))
}

pub fn escape_pointer_segment(segment: impl AsRef<str>) -> String {
    segment.as_ref().replace('~', "~0").replace('/', "~1")
}
