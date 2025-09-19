use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use tf_oracles_core::{
    diff_values, err, ok, pointer_from_segments, with_trace, DiffResult, Oracle, OracleCtx,
    OracleResult,
};

const FAILURE_CODE: &str = "E_TRANSPORT_DRIFT";
const SERIALIZE_ERROR_CODE: &str = "E_TRANSPORT_SERIALIZE";
const DECODE_ERROR_CODE: &str = "E_TRANSPORT_DECODE";
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
    pub encoded: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TransportReport {
    #[serde(rename = "casesChecked")]
    pub cases_checked: usize,
    #[serde(rename = "roundTripsChecked")]
    pub round_trips_checked: usize,
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
    pub error: Option<TransportError>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TransportError {
    pub code: String,
    pub message: String,
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
    let missing_value = Value::String(MISSING_VALUE.to_string());

    for transport_case in &input.cases {
        cases_checked += 1;
        round_trips_checked += 1;

        let original = ctx.canonicalize_value(transport_case.value.clone());
        let serialization = if let Some(encoded) = &transport_case.encoded {
            Ok(encoded.clone())
        } else {
            serialize_value(&transport_case.value)
        };

        let encoded = match serialization {
            Ok(value) => value,
            Err(error) => {
                drifts.push(TransportDrift {
                    case: transport_case.name.clone(),
                    seed: transport_case.seed.clone(),
                    pointer: pointer_from_segments(&Vec::<String>::new()),
                    before: original.clone(),
                    after: Value::String(UNSERIALIZABLE.to_string()),
                    error: Some(error),
                });
                continue;
            }
        };

        let parsed = parse_json(&encoded);
        let parsed_value = match parsed {
            Ok(value) => value,
            Err(error) => {
                drifts.push(TransportDrift {
                    case: transport_case.name.clone(),
                    seed: transport_case.seed.clone(),
                    pointer: pointer_from_segments(&Vec::<String>::new()),
                    before: original.clone(),
                    after: Value::String(INVALID_JSON.to_string()),
                    error: Some(error),
                });
                continue;
            }
        };

        let normalized = ctx.canonicalize_value(parsed_value);
        if let Some(diff) = diff_values(&original, &normalized, &missing_value) {
            drifts.push(build_drift(transport_case, diff));
        }
    }

    if drifts.is_empty() {
        let report = TransportReport {
            cases_checked,
            round_trips_checked,
        };
        return ok(report, std::iter::empty::<&str>());
    }

    let details = json!({ "drifts": drifts });
    let failure = err(
        FAILURE_CODE,
        "Transport round-trip drift detected",
        Some(details),
    );
    let trace = drifts
        .iter()
        .take(5)
        .map(|drift| format!("case:{}:{}", drift.case, drift.pointer));
    with_trace(failure, trace).into()
}

fn build_drift(case: &TransportCase, diff: DiffResult) -> TransportDrift {
    TransportDrift {
        case: case.name.clone(),
        seed: case.seed.clone(),
        pointer: diff.pointer,
        before: diff.left,
        after: diff.right,
        error: None,
    }
}

fn serialize_value(value: &Value) -> Result<String, TransportError> {
    serde_json::to_string(value).map_err(|error| TransportError {
        code: SERIALIZE_ERROR_CODE.to_string(),
        message: error.to_string(),
    })
}

fn parse_json(encoded: &str) -> Result<Value, TransportError> {
    serde_json::from_str(encoded).map_err(|error| TransportError {
        code: DECODE_ERROR_CODE.to_string(),
        message: error.to_string(),
    })
}
