use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use tf_oracles_core::{
    diff_canonical, err, ok, pointer_from_segments, with_trace, DiffOptions, Oracle, OracleCtx,
    OracleResult,
};

const FAILURE_CODE: &str = "E_TRANSPORT_DRIFT";
const SERIALIZE_CODE: &str = "E_TRANSPORT_SERIALIZE";
const DECODE_CODE: &str = "E_TRANSPORT_DECODE";
const UNSERIALIZABLE: &str = "[unserializable]";
const INVALID_JSON: &str = "[invalid-json]";
const MISSING_VALUE: &str = "[missing]";

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct TransportInput {
    #[serde(default)]
    pub cases: Vec<TransportCase>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransportCase {
    pub name: String,
    #[serde(default)]
    pub seed: Option<String>,
    pub value: Value,
    #[serde(default)]
    pub encoded: Option<Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TransportReport {
    #[serde(rename = "casesChecked")]
    pub cases_checked: usize,
    #[serde(rename = "roundTripsChecked")]
    pub round_trips_checked: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TransportIssue {
    pub code: String,
    pub message: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TransportDrift {
    pub case: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub seed: Option<String>,
    pub pointer: String,
    pub before: Value,
    pub after: Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub issue: Option<TransportIssue>,
}

#[derive(Debug, Default)]
pub struct TransportOracle;

impl TransportOracle {
    pub fn new() -> Self {
        Self
    }
}

impl Oracle<TransportInput, TransportReport> for TransportOracle {
    fn check(&self, input: &TransportInput, ctx: &OracleCtx) -> OracleResult<TransportReport> {
        check_transport(input, ctx)
    }
}

pub fn check_transport(input: &TransportInput, ctx: &OracleCtx) -> OracleResult<TransportReport> {
    let mut cases_checked = 0usize;
    let mut round_trips_checked = 0usize;
    let mut drifts = Vec::new();
    let missing = Value::String(MISSING_VALUE.to_string());

    for transport_case in &input.cases {
        cases_checked += 1;
        round_trips_checked += 1;
        let original = ctx.canonicalize_value(transport_case.value.clone());

        let serialization = if let Some(encoded) = &transport_case.encoded {
            ensure_pre_encoded(encoded)
        } else {
            serialize_value(&transport_case.value)
        };

        let encoded = match serialization {
            SerializeOutcome::Ok(text) => text,
            SerializeOutcome::Err(issue) => {
                drifts.push(TransportDrift {
                    case: transport_case.name.clone(),
                    seed: transport_case.seed.clone(),
                    pointer: pointer_from_segments(&[] as &[&str]),
                    before: original.clone(),
                    after: Value::String(UNSERIALIZABLE.to_string()),
                    issue: Some(issue),
                });
                continue;
            }
        };

        let parsed = match parse_json(&encoded) {
            ParseOutcome::Ok(value) => value,
            ParseOutcome::Err(issue) => {
                drifts.push(TransportDrift {
                    case: transport_case.name.clone(),
                    seed: transport_case.seed.clone(),
                    pointer: pointer_from_segments(&[] as &[&str]),
                    before: original.clone(),
                    after: Value::String(INVALID_JSON.to_string()),
                    issue: Some(issue),
                });
                continue;
            }
        };

        let normalized = ctx.canonicalize_value(parsed);
        if let Some(diff) = diff_canonical(
            &original,
            &normalized,
            DiffOptions {
                missing_value: Some(&missing),
            },
        ) {
            drifts.push(TransportDrift {
                case: transport_case.name.clone(),
                seed: transport_case.seed.clone(),
                pointer: diff.pointer,
                before: diff.left,
                after: diff.right,
                issue: None,
            });
        }
    }

    if drifts.is_empty() {
        let report = TransportReport {
            cases_checked,
            round_trips_checked,
        };
        return ok(report, std::iter::empty::<&str>());
    }

    let trace: Vec<String> = drifts
        .iter()
        .take(5)
        .map(|drift| format!("case:{}:{}", drift.case, drift.pointer))
        .collect();
    let details = json!({ "drifts": drifts });
    let failure = err(
        FAILURE_CODE,
        "Transport round-trip drift detected",
        Some(details),
    );
    with_trace(failure, trace).into()
}

enum SerializeOutcome {
    Ok(String),
    Err(TransportIssue),
}

fn ensure_pre_encoded(value: &Value) -> SerializeOutcome {
    match value {
        Value::String(text) => SerializeOutcome::Ok(text.clone()),
        other => SerializeOutcome::Err(TransportIssue {
            code: SERIALIZE_CODE.to_string(),
            message: format!(
                "pre-encoded payload must be a string (received {:?})",
                other
            ),
        }),
    }
}

fn serialize_value(value: &Value) -> SerializeOutcome {
    match serde_json::to_string(value) {
        Ok(encoded) => SerializeOutcome::Ok(encoded),
        Err(error) => SerializeOutcome::Err(TransportIssue {
            code: SERIALIZE_CODE.to_string(),
            message: error.to_string(),
        }),
    }
}

enum ParseOutcome {
    Ok(Value),
    Err(TransportIssue),
}

fn parse_json(text: &str) -> ParseOutcome {
    match serde_json::from_str::<Value>(text) {
        Ok(value) => ParseOutcome::Ok(value),
        Err(error) => ParseOutcome::Err(TransportIssue {
            code: DECODE_CODE.to_string(),
            message: error.to_string(),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_drift_from_pre_encoded_payload() {
        let input = TransportInput {
            cases: vec![TransportCase {
                name: "encoded".to_string(),
                seed: None,
                value: json!({ "keep": true }),
                encoded: Some(Value::String("{}".to_string())),
            }],
        };
        let ctx = OracleCtx::new("seed");
        let result = check_transport(&input, &ctx);
        match result {
            OracleResult::Failure(failure) => {
                assert_eq!(failure.error.code, FAILURE_CODE);
            }
            _ => panic!("expected failure"),
        }
    }

    #[test]
    fn handles_invalid_json() {
        let input = TransportInput {
            cases: vec![TransportCase {
                name: "invalid".to_string(),
                seed: None,
                value: json!({ "ok": true }),
                encoded: Some(Value::String("{".to_string())),
            }],
        };
        let ctx = OracleCtx::new("seed");
        let result = check_transport(&input, &ctx);
        match result {
            OracleResult::Failure(failure) => {
                assert_eq!(failure.error.code, FAILURE_CODE);
            }
            _ => panic!("expected failure"),
        }
    }

    #[test]
    fn reports_success_when_round_trip_matches() {
        let input = TransportInput {
            cases: vec![TransportCase {
                name: "ok".to_string(),
                seed: None,
                value: json!({ "vector": [1, 2, 3] }),
                encoded: None,
            }],
        };
        let ctx = OracleCtx::new("seed");
        let result = check_transport(&input, &ctx);
        match result {
            OracleResult::Success(success) => {
                assert_eq!(success.value.cases_checked, 1);
                assert_eq!(success.value.round_trips_checked, 1);
            }
            _ => panic!("expected success"),
        }
    }

    #[test]
    fn rejects_non_string_pre_encoded_values() {
        let input = TransportInput {
            cases: vec![TransportCase {
                name: "type".to_string(),
                seed: None,
                value: json!({ "ok": true }),
                encoded: Some(json!(42)),
            }],
        };
        let ctx = OracleCtx::new("seed");
        let result = check_transport(&input, &ctx);
        match result {
            OracleResult::Failure(failure) => {
                assert_eq!(failure.error.code, FAILURE_CODE);
            }
            _ => panic!("expected failure"),
        }
    }
}
