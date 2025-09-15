use serde::{Deserialize, Serialize};
use serde_json::{Map, Number, Value};
use thiserror::Error;

pub trait Oracle<I, O>
where
    O: Serialize,
{
    fn check(&self, input: &I, ctx: &OracleCtx) -> OracleResult<O>;
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct OracleError {
    pub code: String,
    pub explain: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub details: Option<Value>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct OracleFailure {
    pub ok: bool,
    pub error: OracleError,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub trace: Option<Vec<String>>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct OracleSuccess<T>
where
    T: Serialize,
{
    pub ok: bool,
    pub value: T,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub warnings: Option<Vec<String>>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum OracleResult<T>
where
    T: Serialize,
{
    Success(OracleSuccess<T>),
    Failure(OracleFailure),
}

impl<T> From<OracleFailure> for OracleResult<T>
where
    T: Serialize,
{
    fn from(value: OracleFailure) -> Self {
        OracleResult::Failure(value)
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct OracleCtx {
    pub seed: String,
    pub now: i64,
}

impl OracleCtx {
    pub fn new(seed: impl Into<String>) -> Self {
        Self {
            seed: seed.into(),
            now: 0,
        }
    }

    pub fn with_now(mut self, now: i64) -> Self {
        self.now = now;
        self
    }

    pub fn seed(&self) -> &str {
        &self.seed
    }

    pub fn now(&self) -> i64 {
        self.now
    }

    pub fn canonicalize<T>(&self, value: &T) -> Result<Value, CanonError>
    where
        T: Serialize,
    {
        canonicalize(value)
    }

    pub fn canonicalize_value(&self, value: Value) -> Value {
        canonicalize_value(value)
    }
}

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

pub fn ok<T, I>(value: T, warnings: I) -> OracleResult<T>
where
    T: Serialize,
    I: IntoIterator,
    I::Item: AsRef<str>,
{
    let collected = dedupe(warnings.into_iter());
    let warnings_field = if collected.is_empty() {
        None
    } else {
        Some(collected)
    };

    OracleResult::Success(OracleSuccess {
        ok: true,
        value,
        warnings: warnings_field,
    })
}

pub fn err(code: &str, explain: &str, details: Option<Value>) -> OracleFailure {
    OracleFailure {
        ok: false,
        error: OracleError {
            code: normalize_code(code),
            explain: explain.trim().to_string(),
            details,
        },
        trace: None,
    }
}

pub fn err_with_details<T>(code: &str, explain: &str, details: Option<T>) -> Result<OracleFailure, CanonError>
where
    T: Serialize,
{
    let details_value = match details {
        Some(payload) => Some(canonicalize(&payload)?),
        None => None,
    };
    Ok(err(code, explain, details_value))
}

pub fn with_trace<I>(mut failure: OracleFailure, trace: I) -> OracleFailure
where
    I: IntoIterator,
    I::Item: AsRef<str>,
{
    let mut combined = failure.trace.unwrap_or_default();
    for entry in trace {
        combined.push(entry.as_ref().to_string());
    }
    let merged = dedupe(combined.iter());
    if merged.is_empty() {
        failure.trace = None;
    } else {
        failure.trace = Some(merged);
    }
    failure
}

fn canonicalize_object(map: Map<String, Value>) -> Value {
    let mut entries: Vec<(String, Value)> = map.into_iter().collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));

    let canonical: Map<String, Value> = entries
        .into_iter()
        .map(|(key, value)| (key, canonicalize_value(value)))
        .collect();
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

fn dedupe<I>(source: I) -> Vec<String>
where
    I: IntoIterator,
    I::Item: AsRef<str>,
{
    let mut result = Vec::new();
    for entry in source {
        let trimmed = entry.as_ref().trim();
        if trimmed.is_empty() {
            continue;
        }
        if result.iter().any(|existing| existing == trimmed) {
            continue;
        }
        result.push(trimmed.to_string());
    }
    result
}

fn normalize_code(code: &str) -> String {
    let trimmed = code.trim();
    if trimmed.is_empty() {
        "E_UNKNOWN".to_string()
    } else {
        trimmed.to_ascii_uppercase()
    }
}
