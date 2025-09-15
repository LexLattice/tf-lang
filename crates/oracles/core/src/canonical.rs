use serde::Serialize;
use serde_json::{Map, Value};

fn canonicalize_number(value: &serde_json::Number) -> Value {
  Value::Number(value.clone())
}

fn canonicalize_array(values: &[Value]) -> Value {
  Value::Array(values.iter().map(canonicalize_value).collect())
}

fn canonicalize_object(values: &Map<String, Value>) -> Value {
  let mut entries: Vec<(String, Value)> = values
    .iter()
    .map(|(key, value)| (key.clone(), canonicalize_value(value)))
    .collect();
  entries.sort_by(|a, b| a.0.cmp(&b.0));
  let mut map = Map::with_capacity(entries.len());
  for (key, value) in entries {
    map.insert(key, value);
  }
  Value::Object(map)
}

pub fn canonicalize_value(value: &Value) -> Value {
  match value {
    Value::Null => Value::Null,
    Value::Bool(b) => Value::Bool(*b),
    Value::Number(n) => canonicalize_number(n),
    Value::String(s) => Value::String(s.clone()),
    Value::Array(values) => canonicalize_array(values),
    Value::Object(map) => canonicalize_object(map),
  }
}

pub fn canonicalize<T>(value: &T) -> Result<Value, serde_json::Error>
where
  T: Serialize,
{
  match serde_json::to_value(value) {
    Ok(value) => Ok(canonicalize_value(&value)),
    Err(err) => {
      if err.is_data() {
        Ok(Value::Null)
      } else {
        Err(err)
      }
    }
  }
}

pub fn canonical_string(value: &Value) -> Result<String, serde_json::Error> {
  serde_json::to_string(&canonicalize_value(value))
}

pub fn canonical_bytes(value: &Value) -> Result<Vec<u8>, serde_json::Error> {
  canonical_string(value).map(|s| s.into_bytes())
}

