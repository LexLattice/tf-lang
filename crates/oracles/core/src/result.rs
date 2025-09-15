use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::canonical::canonicalize_value;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OracleError {
  pub code: String,
  pub explain: String,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub details: Option<Value>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OracleFailure {
  pub ok: bool,
  pub error: OracleError,
  #[serde(skip_serializing_if = "Vec::is_empty", default)]
  pub trace: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OracleOk<T> {
  pub ok: bool,
  pub value: T,
  #[serde(skip_serializing_if = "Vec::is_empty", default)]
  pub warnings: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum OracleResult<T> {
  Ok(OracleOk<T>),
  Err(OracleFailure),
}

fn normalize_strings<S>(values: S) -> Vec<String>
where
  S: IntoIterator,
  S::Item: AsRef<str>,
{
  let mut set = BTreeSet::new();
  for value in values {
    let trimmed = value.as_ref().trim();
    if trimmed.is_empty() {
      continue;
    }
    set.insert(trimmed.to_owned());
  }
  set.into_iter().collect()
}

pub fn ok<T>(value: T) -> OracleResult<T> {
  OracleResult::Ok(OracleOk {
    ok: true,
    value,
    warnings: Vec::new(),
  })
}

pub fn err<T>(failure: OracleFailure) -> OracleResult<T> {
  OracleResult::Err(failure)
}

pub fn ok_with_warnings<T, I>(value: T, warnings: I) -> OracleResult<T>
where
  I: IntoIterator,
  I::Item: AsRef<str>,
{
  let normalized = normalize_strings(warnings);
  OracleResult::Ok(OracleOk {
    ok: true,
    value,
    warnings: normalized,
  })
}

pub fn merge_warnings<T, I>(result: OracleOk<T>, extra: I) -> OracleOk<T>
where
  I: IntoIterator,
  I::Item: AsRef<str>,
{
  let OracleOk { value, mut warnings, .. } = result;
  warnings.extend(extra.into_iter().map(|s| s.as_ref().to_owned()));
  let normalized = normalize_strings(warnings.iter().map(|s| s.as_str()));
  OracleOk {
    ok: true,
    value,
    warnings: normalized,
  }
}

pub fn error(code: impl Into<String>, explain: impl Into<String>) -> OracleError {
  OracleError {
    code: code.into(),
    explain: explain.into(),
    details: None,
  }
}

pub fn error_with_details<T>(
  code: impl Into<String>,
  explain: impl Into<String>,
  details: Option<T>,
) -> Result<OracleError, serde_json::Error>
where
  T: Serialize,
{
  let base = error(code, explain);
  match details {
    Some(value) => {
      let as_value = match serde_json::to_value(value) {
        Ok(val) => val,
        Err(err) if err.is_data() => Value::Null,
        Err(err) => return Err(err),
      };
      Ok(OracleError {
        details: Some(canonicalize_value(&as_value)),
        ..base
      })
    }
    None => Ok(base),
  }
}

pub fn failure(
  code: impl Into<String>,
  explain: impl Into<String>,
  details: Option<Value>,
  trace: impl IntoIterator<Item = impl AsRef<str>>,
) -> OracleFailure {
  let err = OracleError {
    details: details.map(|value| canonicalize_value(&value)),
    ..error(code, explain)
  };
  OracleFailure {
    ok: false,
    error: err,
    trace: normalize_strings(trace),
  }
}

pub fn failure_result<T>(
  code: impl Into<String>,
  explain: impl Into<String>,
  details: Option<Value>,
  trace: impl IntoIterator<Item = impl AsRef<str>>,
) -> OracleResult<T> {
  err(failure(code, explain, details, trace))
}

pub fn from_error(err: &OracleError, trace: impl IntoIterator<Item = impl AsRef<str>>) -> OracleFailure {
  OracleFailure {
    ok: false,
    error: OracleError {
      code: err.code.clone(),
      explain: err.explain.clone(),
      details: err.details.as_ref().map(|value| canonicalize_value(value)),
    },
    trace: normalize_strings(trace),
  }
}

pub fn is_ok<T>(result: &OracleResult<T>) -> bool {
  matches!(result, OracleResult::Ok(_))
}

pub fn map_value<A, B>(result: OracleResult<A>, mapper: impl FnOnce(A) -> B) -> OracleResult<B> {
  match result {
    OracleResult::Ok(ok) => {
      let mapped = mapper(ok.value);
      OracleResult::Ok(OracleOk {
        ok: true,
        value: mapped,
        warnings: ok.warnings,
      })
    }
    OracleResult::Err(err) => OracleResult::Err(err),
  }
}

pub fn format_failure(result: &OracleResult<Value>) -> Option<String> {
  match result {
    OracleResult::Ok(_) => None,
    OracleResult::Err(failure) => {
      let mut msg = format!("{}: {}", failure.error.code, failure.error.explain);
      if let Some(details) = &failure.error.details {
        if let Ok(json) = serde_json::to_string(details) {
          msg.push_str(" | details=");
          msg.push_str(&json);
        }
      }
      Some(msg)
    }
  }
}

