use serde::Serialize;
use serde_json::{Map, Value};

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct OracleOk<T>
where
    T: Serialize,
{
    pub ok: bool,
    pub value: T,
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub warnings: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct OracleErrorDetail {
    pub code: String,
    pub explain: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub details: Option<Value>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct OracleErr {
    pub ok: bool,
    pub error: OracleErrorDetail,
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub trace: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(untagged)]
pub enum OracleOutcome<T>
where
    T: Serialize,
{
    Ok(OracleOk<T>),
    Err(OracleErr),
}

impl<T> From<OracleOk<T>> for OracleOutcome<T>
where
    T: Serialize,
{
    fn from(value: OracleOk<T>) -> Self {
        OracleOutcome::Ok(value)
    }
}

impl<T> From<OracleErr> for OracleOutcome<T>
where
    T: Serialize,
{
    fn from(value: OracleErr) -> Self {
        OracleOutcome::Err(value)
    }
}

pub trait Oracle<I, O>
where
    O: Serialize,
{
    fn check(&self, input: I, ctx: &OracleCtx) -> OracleOutcome<O>;
}

#[derive(Debug, Clone)]
pub struct OracleCtx {
    pub seed: String,
    pub now: i64,
}

impl OracleCtx {
    pub fn new(seed: impl Into<String>, now: i64) -> Self {
        Self {
            seed: seed.into(),
            now,
        }
    }

    pub fn canonicalize<T>(&self, value: &T) -> serde_json::Result<Value>
    where
        T: Serialize,
    {
        canonicalize(value)
    }
}

#[derive(Debug, Default, Clone)]
pub struct ErrorOptions {
    pub details: Option<Value>,
    pub trace: Vec<String>,
}

pub fn ok<T>(value: T) -> OracleOk<T>
where
    T: Serialize,
{
    OracleOk {
        ok: true,
        value,
        warnings: Vec::new(),
    }
}

pub fn ok_with_warnings<T, I>(value: T, warnings: I) -> OracleOk<T>
where
    T: Serialize,
    I: IntoIterator,
    I::Item: Into<String>,
{
    let mut collected = Vec::new();
    for warning in warnings {
        collected.push(warning.into());
    }
    OracleOk {
        ok: true,
        value,
        warnings: collected,
    }
}

pub fn err(
    code: impl Into<String>,
    explain: impl Into<String>,
    options: ErrorOptions,
) -> OracleErr {
    OracleErr {
        ok: false,
        error: OracleErrorDetail {
            code: code.into(),
            explain: explain.into(),
            details: options.details,
        },
        trace: options.trace,
    }
}

pub fn canonicalize<T>(value: &T) -> serde_json::Result<Value>
where
    T: Serialize,
{
    let raw = serde_json::to_value(value)?;
    Ok(canonicalize_value(raw))
}

pub fn canonical_json_string<T>(value: &T) -> serde_json::Result<String>
where
    T: Serialize,
{
    let canonical = canonicalize(value)?;
    serde_json::to_string(&canonical)
}

fn canonicalize_value(value: Value) -> Value {
    match value {
        Value::Null => Value::Null,
        Value::Bool(_) => value,
        Value::Number(n) => canonicalize_number(n),
        Value::String(_) => value,
        Value::Array(items) => Value::Array(items.into_iter().map(canonicalize_value).collect()),
        Value::Object(map) => Value::Object(canonicalize_map(map)),
    }
}

fn canonicalize_number(number: serde_json::Number) -> Value {
    if number.is_i64() || number.is_u64() {
        return Value::Number(number);
    }
    if let Some(f) = number.as_f64() {
        if !f.is_finite() {
            return Value::String(f.to_string());
        }
        if f.trunc() == f {
            if let Some(int_value) = serde_json::Number::from_f64(f) {
                return Value::Number(int_value);
            }
        }
        Value::String(format!("{:.12}", f))
    } else {
        Value::Number(number)
    }
}

fn canonicalize_map(map: Map<String, Value>) -> Map<String, Value> {
    let mut entries: Vec<(String, Value)> = map.into_iter().collect();
    entries.sort_by(|(a, _), (b, _)| a.cmp(b));
    let mut canonical = Map::new();
    for (key, value) in entries {
        canonical.insert(key, canonicalize_value(value));
    }
    canonical
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonicalizes_numbers_and_keys() {
        let value = serde_json::json!({
            "z": 4,
            "a": 1,
            "list": [3, 1.2345678901234],
            "nested": {
                "c": 3,
                "b": 2,
                "a": 1
            },
            "maybe": null
        });
        let canonical = canonicalize(&value).expect("canonicalize");
        assert_eq!(
            canonical,
            serde_json::json!({
                "a": 1,
                "list": [3, "1.234567890123"],
                "maybe": null,
                "nested": {"a": 1, "b": 2, "c": 3},
                "z": 4
            })
        );
    }

    #[test]
    fn builds_ok_and_err() {
        let ok_value = ok(serde_json::json!({"final": 1}));
        assert!(ok_value.ok);
        assert_eq!(ok_value.warnings.len(), 0);

        let with_warnings = ok_with_warnings(1, ["warn-1", "warn-2"]);
        assert_eq!(with_warnings.warnings.len(), 2);

        let mut options = ErrorOptions::default();
        options.trace = vec!["step-1".to_string(), "step-2".to_string()];
        options.details = Some(serde_json::json!({"diff": 1}));
        let error = err("E_TEST", "failed", options.clone());
        assert!(!error.ok);
        assert_eq!(error.trace, options.trace);
    }

    #[test]
    fn ctx_canonicalizes() {
        let ctx = OracleCtx::new("0x1", 0);
        let canonical = ctx
            .canonicalize(&serde_json::json!({"b": 2, "a": 1.5}))
            .expect("canonical");
        assert_eq!(
            canonical,
            serde_json::json!({"a": "1.500000000000", "b": 2})
        );
    }
}
