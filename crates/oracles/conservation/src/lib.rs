use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use serde_json::{json, Map, Value};
use tf_oracles_core::{err, ok, with_trace, Oracle, OracleCtx, OracleResult, MISSING_VALUE};

const FAILURE_CODE: &str = "E_NOT_CONSERVED";

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ConservationInput {
    #[serde(default)]
    pub keys: Vec<String>,
    #[serde(default)]
    pub before: Value,
    #[serde(default)]
    pub after: Value,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
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
    let before = canonicalize_snapshot(&input.before, ctx);
    let after = canonicalize_snapshot(&input.after, ctx);
    let keys = collect_keys(&input.keys, &before, &after);

    let mut violations: Vec<ConservationViolation> = Vec::new();

    for key in keys.iter() {
        let before_value = before
            .get(key)
            .cloned()
            .unwrap_or_else(|| Value::String(MISSING_VALUE.to_string()));
        let after_value = after
            .get(key)
            .cloned()
            .unwrap_or_else(|| Value::String(MISSING_VALUE.to_string()));

        if before_value == after_value {
            continue;
        }

        violations.push(ConservationViolation {
            key: key.clone(),
            before: before_value.clone(),
            after: after_value.clone(),
            delta: compute_delta(&before_value, &after_value),
        });
    }

    if violations.is_empty() {
        return ok(
            ConservationReport {
                keys_checked: keys.len(),
            },
            std::iter::empty::<&str>(),
        );
    }

    let details = json!({ "violations": violations });
    let failure = err(FAILURE_CODE, "Conservation violated", Some(details));
    let trace = violations
        .iter()
        .take(5)
        .map(|violation| format!("key:{}", violation.key));
    with_trace(failure, trace).into()
}

fn canonicalize_snapshot(value: &Value, ctx: &OracleCtx) -> Map<String, Value> {
    match value {
        Value::Object(map) => map
            .iter()
            .filter_map(|(key, entry)| {
                if entry.is_null() {
                    Some((key.clone(), Value::Null))
                } else {
                    Some((key.clone(), ctx.canonicalize_value(entry.clone())))
                }
            })
            .collect(),
        _ => Map::new(),
    }
}

fn collect_keys(
    declared: &[String],
    before: &Map<String, Value>,
    after: &Map<String, Value>,
) -> Vec<String> {
    if !declared.is_empty() {
        let mut filtered: Vec<String> = declared
            .iter()
            .filter(|key| !key.trim().is_empty())
            .cloned()
            .collect();
        filtered.sort();
        filtered.dedup();
        return filtered;
    }

    let mut set = BTreeSet::new();
    set.extend(before.keys().cloned());
    set.extend(after.keys().cloned());
    set.into_iter().collect()
}

fn compute_delta(before: &Value, after: &Value) -> Option<f64> {
    match (extract_number(before), extract_number(after)) {
        (Some(left), Some(right)) => {
            let raw = right - left;
            let formatted = (raw * 1_000_000_000_000.0).round() / 1_000_000_000_000.0;
            if formatted == -0.0 {
                Some(0.0)
            } else {
                Some(formatted)
            }
        }
        _ => None,
    }
}

fn extract_number(value: &Value) -> Option<f64> {
    match value {
        Value::Number(num) => num.as_f64().filter(|v| v.is_finite()),
        _ => None,
    }
}
