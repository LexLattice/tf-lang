use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use tf_oracles_core::{
    diff_canonical, err, ok, with_trace, DiffOptions, Oracle, OracleCtx, OracleResult,
};

const FAILURE_CODE: &str = "E_NOT_IDEMPOTENT";
const MISSING_VALUE: &str = "[missing]";

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct IdempotenceInput {
    #[serde(default)]
    pub cases: Vec<IdempotenceCase>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IdempotenceCase {
    pub name: String,
    #[serde(default)]
    pub seed: Option<String>,
    #[serde(default)]
    pub applications: Vec<IdempotenceApplication>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IdempotenceApplication {
    #[serde(default)]
    pub iteration: Option<i64>,
    pub value: Value,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct IdempotenceReport {
    #[serde(rename = "casesChecked")]
    pub cases_checked: usize,
    #[serde(rename = "applicationsChecked")]
    pub applications_checked: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct IdempotenceMismatch {
    pub case: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub seed: Option<String>,
    pub iteration: i64,
    pub pointer: String,
    pub expected: Value,
    pub actual: Value,
}

#[derive(Debug, Default)]
pub struct IdempotenceOracle;

impl IdempotenceOracle {
    pub fn new() -> Self {
        Self
    }
}

impl Oracle<IdempotenceInput, IdempotenceReport> for IdempotenceOracle {
    fn check(&self, input: &IdempotenceInput, ctx: &OracleCtx) -> OracleResult<IdempotenceReport> {
        check_idempotence(input, ctx)
    }
}

pub fn check_idempotence(
    input: &IdempotenceInput,
    ctx: &OracleCtx,
) -> OracleResult<IdempotenceReport> {
    let mut cases_checked = 0usize;
    let mut applications_checked = 0usize;
    let mut mismatches = Vec::new();
    let missing = Value::String(MISSING_VALUE.to_string());

    for idempotence_case in &input.cases {
        cases_checked += 1;
        let applications = canonicalize_applications(&idempotence_case.applications, ctx);
        if applications.len() <= 1 {
            continue;
        }

        let baseline = &applications[0];
        for candidate in applications.iter().skip(1) {
            applications_checked += 1;
            if let Some(diff) = diff_canonical(
                &baseline.value,
                &candidate.value,
                DiffOptions {
                    missing_value: Some(&missing),
                },
            ) {
                mismatches.push(IdempotenceMismatch {
                    case: idempotence_case.name.clone(),
                    seed: idempotence_case.seed.clone(),
                    iteration: candidate.iteration,
                    pointer: diff.pointer,
                    expected: diff.left,
                    actual: diff.right,
                });
            }
        }
    }

    if mismatches.is_empty() {
        let report = IdempotenceReport {
            cases_checked,
            applications_checked,
        };
        return ok(report, std::iter::empty::<&str>());
    }

    let trace: Vec<String> = mismatches
        .iter()
        .take(5)
        .map(|mismatch| format!("case:{}:iteration:{}", mismatch.case, mismatch.iteration))
        .collect();
    let details = json!({ "mismatches": mismatches });
    let failure = err(FAILURE_CODE, "Repeated application diverged", Some(details));
    with_trace(failure, trace).into()
}

#[derive(Debug)]
struct CanonicalApplication {
    iteration: i64,
    value: Value,
}

fn canonicalize_applications(
    applications: &[IdempotenceApplication],
    ctx: &OracleCtx,
) -> Vec<CanonicalApplication> {
    applications
        .iter()
        .enumerate()
        .map(|(index, application)| CanonicalApplication {
            iteration: application.iteration.unwrap_or(index as i64),
            value: ctx.canonicalize_value(application.value.clone()),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reports_drift_pointer() {
        let input = IdempotenceInput {
            cases: vec![IdempotenceCase {
                name: "drift".to_string(),
                seed: None,
                applications: vec![
                    IdempotenceApplication {
                        iteration: Some(0),
                        value: json!({ "count": 1 }),
                    },
                    IdempotenceApplication {
                        iteration: Some(1),
                        value: json!({ "count": 2 }),
                    },
                ],
            }],
        };
        let ctx = OracleCtx::new("seed");
        let result = check_idempotence(&input, &ctx);
        match result {
            OracleResult::Failure(failure) => {
                assert_eq!(failure.error.code, FAILURE_CODE);
                let details = failure.error.details.expect("details");
                assert!(details["mismatches"].is_array());
            }
            _ => panic!("expected failure"),
        }
    }

    #[test]
    fn pointer_at_root_for_scalar_drift() {
        let input = IdempotenceInput {
            cases: vec![IdempotenceCase {
                name: "root".to_string(),
                seed: None,
                applications: vec![
                    IdempotenceApplication {
                        iteration: Some(0),
                        value: json!(1),
                    },
                    IdempotenceApplication {
                        iteration: Some(1),
                        value: json!(2),
                    },
                ],
            }],
        };
        let ctx = OracleCtx::new("seed");
        let result = check_idempotence(&input, &ctx);
        match result {
            OracleResult::Failure(failure) => {
                let pointer = failure.error.details.and_then(|details| {
                    details["mismatches"]
                        .get(0)
                        .and_then(|entry| entry["pointer"].as_str().map(|s| s.to_string()))
                });
                assert_eq!(pointer.as_deref(), Some(""));
            }
            _ => panic!("expected failure"),
        }
    }

    #[test]
    fn passes_when_equal() {
        let input = IdempotenceInput {
            cases: vec![IdempotenceCase {
                name: "equal".to_string(),
                seed: None,
                applications: vec![
                    IdempotenceApplication {
                        iteration: Some(0),
                        value: json!({"v": [1, 2]}),
                    },
                    IdempotenceApplication {
                        iteration: Some(1),
                        value: json!({"v": [1, 2]}),
                    },
                ],
            }],
        };
        let ctx = OracleCtx::new("seed");
        let result = check_idempotence(&input, &ctx);
        match result {
            OracleResult::Success(success) => {
                assert_eq!(success.value.cases_checked, 1);
                assert_eq!(success.value.applications_checked, 1);
            }
            _ => panic!("expected success"),
        }
    }
}
