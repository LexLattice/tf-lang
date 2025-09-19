use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use tf_oracles_core::{diff_canonical, err, ok, with_trace, Oracle, OracleCtx, OracleResult};

const DRIFT_CODE: &str = "E_TRANSPORT_DRIFT";
const SERIALIZE_CODE: &str = "E_TRANSPORT_SERIALIZE";
const DECODE_CODE: &str = "E_TRANSPORT_DECODE";
const UNSERIALIZABLE: &str = "[unserializable]";
const INVALID_JSON: &str = "[invalid-json]";

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

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
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
    let mut round_trips_checked = 0usize;
    let mut drifts: Vec<TransportDrift> = Vec::new();
    let mut failure_code: Option<String> = None;
    let mut failure_message: Option<String> = None;

    for transport_case in &input.cases {
        round_trips_checked += 1;
        let original = ctx.canonicalize_value(transport_case.value.clone());

        let encoded = match &transport_case.encoded {
            Some(Value::String(text)) => text.clone(),
            Some(_) => {
                adopt_failure(
                    &mut failure_code,
                    &mut failure_message,
                    SERIALIZE_CODE,
                    Some("Pre-encoded payload must be a string".to_string()),
                );
                drifts.push(TransportDrift {
                    case: transport_case.name.clone(),
                    seed: transport_case.seed.clone(),
                    pointer: String::new(),
                    before: original.clone(),
                    after: Value::String(UNSERIALIZABLE.to_string()),
                });
                continue;
            }
            None => match serde_json::to_string(&transport_case.value) {
                Ok(value) => value,
                Err(error) => {
                    adopt_failure(
                        &mut failure_code,
                        &mut failure_message,
                        SERIALIZE_CODE,
                        Some(format!("Failed to serialize value: {error}")),
                    );
                    drifts.push(TransportDrift {
                        case: transport_case.name.clone(),
                        seed: transport_case.seed.clone(),
                        pointer: String::new(),
                        before: original.clone(),
                        after: Value::String(UNSERIALIZABLE.to_string()),
                    });
                    continue;
                }
            },
        };

        let parsed: Result<Value, _> = serde_json::from_str(&encoded);
        let parsed = match parsed {
            Ok(value) => value,
            Err(error) => {
                if failure_code.as_deref() != Some(SERIALIZE_CODE) {
                    adopt_failure(
                        &mut failure_code,
                        &mut failure_message,
                        DECODE_CODE,
                        Some(format!("Failed to decode JSON: {error}")),
                    );
                }
                drifts.push(TransportDrift {
                    case: transport_case.name.clone(),
                    seed: transport_case.seed.clone(),
                    pointer: String::new(),
                    before: original.clone(),
                    after: Value::String(INVALID_JSON.to_string()),
                });
                continue;
            }
        };

        let normalized = ctx.canonicalize_value(parsed);
        if let Some(diff) = diff_canonical(&original, &normalized) {
            drifts.push(TransportDrift {
                case: transport_case.name.clone(),
                seed: transport_case.seed.clone(),
                pointer: diff.pointer,
                before: diff.left,
                after: diff.right,
            });
        }
    }

    if drifts.is_empty() {
        return ok(
            TransportReport {
                cases_checked: input.cases.len(),
                round_trips_checked,
            },
            std::iter::empty::<&str>(),
        );
    }

    let code = failure_code.unwrap_or_else(|| DRIFT_CODE.to_string());
    let explain = failure_message.unwrap_or_else(|| default_message(&code).to_string());
    let trace = drifts
        .iter()
        .take(5)
        .map(|drift| format!("case:{}:{}", drift.case, drift.pointer))
        .collect::<Vec<_>>();
    let details = json!({ "drifts": drifts });
    let failure = err(&code, &explain, Some(details));
    with_trace(failure, trace).into()
}

fn adopt_failure(
    code: &mut Option<String>,
    message: &mut Option<String>,
    new_code: &str,
    new_message: Option<String>,
) {
    match code.as_deref() {
        Some(existing) if existing == SERIALIZE_CODE => {
            if new_code == SERIALIZE_CODE && message.is_none() {
                *message = new_message;
            }
        }
        Some(existing) if existing == new_code => {
            if message.is_none() {
                *message = new_message;
            }
        }
        _ => {
            *code = Some(new_code.to_string());
            *message = new_message;
        }
    }
}

fn default_message(code: &str) -> &'static str {
    match code {
        SERIALIZE_CODE => "Transport value could not be serialized",
        DECODE_CODE => "Transport payload could not be decoded",
        _ => "Transport round-trip drift detected",
    }
}
