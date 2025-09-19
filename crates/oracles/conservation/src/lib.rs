use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use tf_oracles_core::{err, ok, with_trace, Oracle, OracleCtx, OracleResult};

const FAILURE_CODE: &str = "E_NOT_CONSERVED";
const MISSING_VALUE: &str = "[missing]";

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ConservationInput {
    #[serde(default)]
    pub version: Option<String>,
    #[serde(default)]
    pub subject: Option<String>,
    #[serde(default)]
    pub keys: Option<Vec<String>>,
    #[serde(default)]
    pub before: Option<BTreeMap<String, Value>>,
    #[serde(default)]
    pub after: Option<BTreeMap<String, Value>>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ConservationReport {
    #[serde(rename = "keysChecked")]
    pub keys_checked: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct ConservationViolation {
    pub key: String,
    pub before: Value,
    pub after: Value,
    pub delta: Option<f64>,
}

#[derive(Debug, Default)]
pub struct ConservationOracle;

impl ConservationOracle {
    pub fn new() -> Self {
        Self
    }
}

impl Oracle<ConservationInput, ConservationReport> for ConservationOracle {
    fn check(
        &self,
        input: &ConservationInput,
        ctx: &OracleCtx,
    ) -> OracleResult<ConservationReport> {
        check_conservation(input, ctx)
    }
}

pub fn check_conservation(
    input: &ConservationInput,
    ctx: &OracleCtx,
) -> OracleResult<ConservationReport> {
    let before = canonicalize_snapshot(input.before.as_ref(), ctx);
    let after = canonicalize_snapshot(input.after.as_ref(), ctx);
    let keys = collect_keys(input.keys.as_ref(), &before, &after);

    let mut violations = Vec::new();

    for key in &keys {
        let has_before = before.contains_key(key);
        let has_after = after.contains_key(key);
        let before_value = if has_before {
            before.get(key).cloned().unwrap_or_else(|| Value::Null)
        } else {
            Value::String(MISSING_VALUE.to_string())
        };
        let after_value = if has_after {
            after.get(key).cloned().unwrap_or_else(|| Value::Null)
        } else {
            Value::String(MISSING_VALUE.to_string())
        };

        if !values_equal(&before_value, &after_value) {
            violations.push(ConservationViolation {
                key: key.clone(),
                delta: compute_delta(&before_value, &after_value),
                before: before_value,
                after: after_value,
            });
        }
    }

    if violations.is_empty() {
        let report = ConservationReport {
            keys_checked: keys.len(),
        };
        return ok(report, std::iter::empty::<&str>());
    }

    let details = json!({ "violations": violations });
    let failure = err(FAILURE_CODE, "Conservation violated", Some(details));
    let trace = violations
        .iter()
        .take(5)
        .map(|violation| format!("key:{}", violation.key));
    with_trace(failure, trace).into()
}

fn canonicalize_snapshot(
    snapshot: Option<&BTreeMap<String, Value>>,
    ctx: &OracleCtx,
) -> BTreeMap<String, Value> {
    let mut result = BTreeMap::new();
    if let Some(map) = snapshot {
        for (key, value) in map {
            let canonical = ctx.canonicalize_value(value.clone());
            result.insert(key.clone(), canonical);
        }
    }
    result
}

fn collect_keys(
    declared: Option<&Vec<String>>,
    before: &BTreeMap<String, Value>,
    after: &BTreeMap<String, Value>,
) -> Vec<String> {
    let mut keys = BTreeSet::new();
    if let Some(declared_keys) = declared {
        for key in declared_keys {
            if !key.is_empty() {
                keys.insert(key.clone());
            }
        }
    } else {
        keys.extend(before.keys().cloned());
        keys.extend(after.keys().cloned());
    }
    keys.into_iter().collect()
}

fn values_equal(left: &Value, right: &Value) -> bool {
    left == right
}

fn compute_delta(left: &Value, right: &Value) -> Option<f64> {
    match (left, right) {
        (Value::Number(a), Value::Number(b)) => {
            if let (Some(left_num), Some(right_num)) = (a.as_f64(), b.as_f64()) {
                let raw = right_num - left_num;
                let rounded = format!("{:.12}", raw).parse::<f64>().unwrap_or(raw);
                if rounded == -0.0 {
                    Some(0.0)
                } else if rounded.is_finite() {
                    Some(rounded)
                } else {
                    None
                }
            } else {
                None
            }
        }
        _ => None,
    }
}
