use serde::Serialize;
use serde_json::{Map, Number, Value};
use std::collections::{BTreeMap, BTreeSet};

use thiserror::Error;

#[derive(Debug, Error)]
pub enum CanonicalizeError {
    #[error("serialization failed: {0}")]
    Serialize(#[from] serde_json::Error),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PointerSeg {
    Key(String),
    Index(usize),
}

pub fn canonicalize(value: &Value) -> Value {
    match value {
        Value::Null => Value::Null,
        Value::Bool(flag) => Value::Bool(*flag),
        Value::Number(num) => canonicalize_number(num),
        Value::String(text) => Value::String(text.clone()),
        Value::Array(entries) => {
            Value::Array(entries.iter().map(|entry| canonicalize(entry)).collect())
        }
        Value::Object(map) => canonicalize_object(map),
    }
}

pub fn canonicalize_from<T>(value: &T) -> Result<Value, CanonicalizeError>
where
    T: Serialize,
{
    let raw = serde_json::to_value(value)?;
    Ok(canonicalize(&raw))
}

pub fn canonical_json(value: &Value) -> String {
    let canonical = canonicalize(value);
    let mut text = serde_json::to_string(&canonical).expect("json string");
    text.push('\n');
    text
}

pub fn pretty_canonical_json(value: &Value) -> String {
    let canonical = canonicalize(value);
    let mut text = serde_json::to_string_pretty(&canonical).expect("json string");
    text.push('\n');
    text
}

pub fn deep_equal(left: &Value, right: &Value) -> Result<(), String> {
    let canonical_left = canonicalize(left);
    let canonical_right = canonicalize(right);
    if let Some(path) = first_diff(&canonical_left, &canonical_right, Vec::new()) {
        Err(pointer_from_segments(&path))
    } else {
        Ok(())
    }
}

pub fn pointer_from_segments(segments: &[PointerSeg]) -> String {
    if segments.is_empty() {
        return "/".to_string();
    }
    let mut pointer = String::new();
    for segment in segments {
        pointer.push('/');
        match segment {
            PointerSeg::Key(key) => pointer.push_str(&escape_segment(key)),
            PointerSeg::Index(index) => pointer.push_str(&index.to_string()),
        }
    }
    pointer
}

pub fn segments_from_pointer(pointer: &str) -> Vec<PointerSeg> {
    if pointer.is_empty() || pointer == "/" {
        return Vec::new();
    }
    let trimmed = pointer.strip_prefix('/').unwrap_or(pointer);
    if trimmed.is_empty() {
        return Vec::new();
    }
    trimmed
        .split('/')
        .map(|segment| parse_segment(&unescape_segment(segment)))
        .collect()
}

fn canonicalize_object(map: &Map<String, Value>) -> Value {
    let mut sorted = BTreeMap::new();
    for (key, value) in map {
        sorted.insert(key.clone(), canonicalize(value));
    }
    Value::Object(sorted.into_iter().collect())
}

fn canonicalize_number(number: &Number) -> Value {
    if number.is_i64() || number.is_u64() {
        return Value::Number(number.clone());
    }

    match number.as_f64() {
        Some(value) => {
            let formatted = format!("{:.12}", value);
            match formatted.parse::<f64>() {
                Ok(parsed) => {
                    if parsed == 0.0 {
                        Value::Number(Number::from(0))
                    } else if let Some(converted) = Number::from_f64(parsed) {
                        Value::Number(converted)
                    } else {
                        Value::String(formatted)
                    }
                }
                Err(_) => Value::String(formatted),
            }
        }
        None => Value::String(number.to_string()),
    }
}

fn first_diff(left: &Value, right: &Value, path: Vec<PointerSeg>) -> Option<Vec<PointerSeg>> {
    if left == right {
        return None;
    }

    match (left, right) {
        (Value::Array(lhs), Value::Array(rhs)) => {
            let limit = lhs.len().min(rhs.len());
            for index in 0..limit {
                let mut next_path = path.clone();
                next_path.push(PointerSeg::Index(index));
                if let Some(diff) = first_diff(&lhs[index], &rhs[index], next_path) {
                    return Some(diff);
                }
            }
            if lhs.len() != rhs.len() {
                let mut next_path = path;
                next_path.push(PointerSeg::Index(limit));
                return Some(next_path);
            }
            None
        }
        (Value::Object(lhs), Value::Object(rhs)) => {
            let mut keys = BTreeSet::new();
            keys.extend(lhs.keys().cloned());
            keys.extend(rhs.keys().cloned());
            for key in keys {
                let mut next_path = path.clone();
                next_path.push(PointerSeg::Key(key.clone()));
                match (lhs.get(&key), rhs.get(&key)) {
                    (Some(lv), Some(rv)) => {
                        if let Some(diff) = first_diff(lv, rv, next_path) {
                            return Some(diff);
                        }
                    }
                    _ => return Some(next_path),
                }
            }
            None
        }
        _ => Some(path),
    }
}

fn escape_segment(segment: &str) -> String {
    segment.replace('~', "~0").replace('/', "~1")
}

fn unescape_segment(segment: &str) -> String {
    segment.replace("~1", "/").replace("~0", "~")
}

fn parse_segment(segment: &str) -> PointerSeg {
    if segment.is_empty() {
        return PointerSeg::Key(String::new());
    }

    if is_array_index(segment) {
        if let Ok(index) = segment.parse::<usize>() {
            return PointerSeg::Index(index);
        }
    }

    PointerSeg::Key(segment.to_string())
}

fn is_array_index(segment: &str) -> bool {
    if segment == "0" {
        return true;
    }
    if segment.starts_with('0') {
        return false;
    }
    segment.chars().all(|ch| ch.is_ascii_digit())
}
