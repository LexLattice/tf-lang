use serde::Serialize;
use std::collections::BTreeMap;

use serde_json::{Map, Number, Value};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum CanonError {
    #[error("serialization failed: {0}")]
    Serialize(#[from] serde_json::Error),
}

pub fn canonicalize<T>(value: &T) -> Result<Value, CanonError>
where
    T: Serialize,
{
    let raw = serde_json::to_value(value)?;
    Ok(canonicalize_value(raw))
}

pub fn canonicalize_value(value: Value) -> Value {
    match value {
        Value::Null => Value::Null,
        Value::Bool(flag) => Value::Bool(flag),
        Value::Number(num) => canonicalize_number(num),
        Value::String(text) => Value::String(text),
        Value::Array(entries) => {
            Value::Array(entries.into_iter().map(canonicalize_value).collect())
        }
        Value::Object(map) => canonicalize_object(map),
    }
}

pub fn canonical_string<T>(value: &T) -> Result<String, CanonError>
where
    T: Serialize,
{
    let canonical = canonicalize(value)?;
    Ok(serde_json::to_string(&canonical)?)
}

fn canonicalize_object(map: Map<String, Value>) -> Value {
    let btree: BTreeMap<String, Value> = map
        .into_iter()
        .map(|(key, value)| (key, canonicalize_value(value)))
        .collect();
    let canonical: Map<String, Value> = btree.into_iter().collect();
    Value::Object(canonical)
}

fn canonicalize_number(number: Number) -> Value {
    if number.is_i64() || number.is_u64() {
        return Value::Number(number);
    }

    match number.as_f64() {
        Some(value) => {
            let formatted = format!("{:.12}", value);
            match formatted.parse::<f64>().ok().and_then(Number::from_f64) {
                Some(parsed) => Value::Number(parsed),
                None => Value::String(formatted),
            }
        }
        None => Value::String(number.to_string()),
    }
}
