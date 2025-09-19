use std::collections::BTreeSet;

use serde_json::Value;

pub const MISSING_VALUE: &str = "[missing]";

#[derive(Debug, Clone, PartialEq)]
pub struct DiffEntry {
    pub pointer: String,
    pub left: Value,
    pub right: Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PointerSegment {
    Key(String),
    Index(usize),
}

impl From<&str> for PointerSegment {
    fn from(value: &str) -> Self {
        Self::Key(value.to_string())
    }
}

impl From<String> for PointerSegment {
    fn from(value: String) -> Self {
        Self::Key(value)
    }
}

impl From<usize> for PointerSegment {
    fn from(value: usize) -> Self {
        Self::Index(value)
    }
}

pub fn escape_pointer_segment(segment: &str) -> String {
    segment.replace('~', "~0").replace('/', "~1")
}

pub fn pointer_from_segments<I>(segments: I) -> String
where
    I: IntoIterator<Item = PointerSegment>,
{
    let mut pointer = String::new();
    for segment in segments {
        pointer.push('/');
        match segment {
            PointerSegment::Key(key) => pointer.push_str(&escape_pointer_segment(&key)),
            PointerSegment::Index(index) => {
                pointer.push_str(&escape_pointer_segment(&index.to_string()))
            }
        }
    }
    pointer
}

pub fn diff_canonical(left: &Value, right: &Value) -> Option<DiffEntry> {
    let mut path: Vec<PointerSegment> = Vec::new();
    diff_canonical_inner(left, right, &mut path)
}

fn diff_canonical_inner(
    left: &Value,
    right: &Value,
    path: &mut Vec<PointerSegment>,
) -> Option<DiffEntry> {
    if left == right {
        return None;
    }

    match (left, right) {
        (Value::Array(left_items), Value::Array(right_items)) => {
            let max = left_items.len().min(right_items.len());
            for index in 0..max {
                path.push(PointerSegment::Index(index));
                let diff = diff_canonical_inner(&left_items[index], &right_items[index], path);
                path.pop();
                if let Some(entry) = diff {
                    return Some(entry);
                }
            }

            if left_items.len() != right_items.len() {
                let index = max;
                let left_value = left_items
                    .get(index)
                    .cloned()
                    .unwrap_or_else(|| Value::String(MISSING_VALUE.to_string()));
                let right_value = right_items
                    .get(index)
                    .cloned()
                    .unwrap_or_else(|| Value::String(MISSING_VALUE.to_string()));
                path.push(PointerSegment::Index(index));
                let pointer = pointer_from_segments(path.clone());
                path.pop();
                return Some(DiffEntry {
                    pointer,
                    left: left_value,
                    right: right_value,
                });
            }
            None
        }
        (Value::Object(left_map), Value::Object(right_map)) => {
            let mut keys = BTreeSet::new();
            keys.extend(left_map.keys().cloned());
            keys.extend(right_map.keys().cloned());
            for key in keys {
                let left_present = left_map.get(&key);
                let right_present = right_map.get(&key);
                path.push(PointerSegment::Key(key.clone()));
                let diff = match (left_present, right_present) {
                    (Some(left_value), Some(right_value)) => {
                        diff_canonical_inner(left_value, right_value, path)
                    }
                    (Some(left_value), None) => Some(DiffEntry {
                        pointer: pointer_from_segments(path.clone()),
                        left: left_value.clone(),
                        right: Value::String(MISSING_VALUE.to_string()),
                    }),
                    (None, Some(right_value)) => Some(DiffEntry {
                        pointer: pointer_from_segments(path.clone()),
                        left: Value::String(MISSING_VALUE.to_string()),
                        right: right_value.clone(),
                    }),
                    (None, None) => None,
                };
                path.pop();
                if let Some(entry) = diff {
                    return Some(entry);
                }
            }
            None
        }
        _ => {
            let pointer = pointer_from_segments(path.clone());
            Some(DiffEntry {
                pointer,
                left: left.clone(),
                right: right.clone(),
            })
        }
    }
}
