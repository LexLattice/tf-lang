use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use serde_json::{json, Map, Value};
use tf_oracles_core::{err, ok, with_trace, Oracle, OracleCtx, OracleResult};

const FAILURE_CODE: &str = "E_NOT_CONSERVED";
const MISSING_VALUE: &str = "[missing]";

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ConservationInput {
    #[serde(default)]
    pub version: Option<String>,
    #[serde(default)]
    pub subject: Option<String>,
    #[serde(default)]
    pub keys: Option<Vec<String>>,
    #[serde(default)]
    pub before: Option<Map<String, Value>>,
    #[serde(default)]
    pub after: Option<Map<String, Value>>,
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
    let before = canonicalize_snapshot(&input.before, ctx);
    let after = canonicalize_snapshot(&input.after, ctx);
    let keys = collect_keys(&input.keys, &before, &after);

    let missing = Value::String(MISSING_VALUE.to_string());
    let mut violations = Vec::new();

    for key in &keys {
        let before_value = before.get(key).cloned().unwrap_or_else(|| missing.clone());
        let after_value = after.get(key).cloned().unwrap_or_else(|| missing.clone());

        if !values_equal(&before_value, &after_value) {
            let delta = compute_delta(&before_value, &after_value);
            violations.push(ConservationViolation {
                key: key.clone(),
                before: before_value,
                after: after_value,
                delta,
            });
        }
    }

    if violations.is_empty() {
        let report = ConservationReport {
            keys_checked: keys.len(),
        };
        return ok(report, std::iter::empty::<&str>());
    }

    let trace: Vec<String> = violations
        .iter()
        .take(5)
        .map(|violation| format!("key:{}", violation.key))
        .collect();
    let details = json!({ "violations": violations });
    let failure = err(FAILURE_CODE, "Conservation violated", Some(details));
    with_trace(failure, trace).into()
}

fn canonicalize_snapshot(
    snapshot: &Option<Map<String, Value>>,
    ctx: &OracleCtx,
) -> BTreeMap<String, Value> {
    let mut result = BTreeMap::new();
    if let Some(map) = snapshot {
        for (key, value) in map {
            result.insert(key.clone(), ctx.canonicalize_value(value.clone()));
        }
    }
    result
}

fn collect_keys(
    declared: &Option<Vec<String>>,
    before: &BTreeMap<String, Value>,
    after: &BTreeMap<String, Value>,
) -> Vec<String> {
    if let Some(list) = declared {
        let filtered: BTreeSet<String> = list
            .iter()
            .filter_map(|key| {
                let trimmed = key.trim();
                if trimmed.is_empty() {
                    None
                } else {
                    Some(trimmed.to_string())
                }
            })
            .collect();
        if !filtered.is_empty() {
            return filtered.into_iter().collect();
        }
    }

    let mut keys = BTreeSet::new();
    keys.extend(before.keys().cloned());
    keys.extend(after.keys().cloned());
    keys.into_iter().collect()
}

fn values_equal(left: &Value, right: &Value) -> bool {
    if left == right {
        return true;
    }
    match (
        tf_oracles_core::canonical_string(left),
        tf_oracles_core::canonical_string(right),
    ) {
        (Ok(a), Ok(b)) => a == b,
        _ => false,
    }
}

fn compute_delta(left: &Value, right: &Value) -> Option<f64> {
    let left_num = left.as_f64()?;
    let right_num = right.as_f64()?;
    if !left_num.is_finite() || !right_num.is_finite() {
        return None;
    }
    let raw = right_num - left_num;
    let formatted = (raw * 1_000_000_000_000.0).round() / 1_000_000_000_000.0;
    Some(if formatted == 0.0 { 0.0 } else { formatted })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_violation() {
        let input = ConservationInput {
            before: Some(Map::from_iter([(String::from("count"), json!(1))])),
            after: Some(Map::from_iter([(String::from("count"), json!(2))])),
            ..Default::default()
        };
        let ctx = OracleCtx::new("seed");
        let result = check_conservation(&input, &ctx);
        match result {
            OracleResult::Failure(failure) => {
                assert_eq!(failure.error.code, FAILURE_CODE);
            }
            _ => panic!("expected failure"),
        }
    }
}
