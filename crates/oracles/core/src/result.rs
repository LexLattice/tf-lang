use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::canonical::{canonicalize, CanonError};

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

pub fn ok<T, I>(value: T, warnings: I) -> OracleResult<T>
where
    T: Serialize,
    I: IntoIterator,
    I::Item: AsRef<str>,
{
    let collected = dedupe(warnings);
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

pub fn err_with_details<T>(
    code: &str,
    explain: &str,
    details: Option<T>,
) -> Result<OracleFailure, CanonError>
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
