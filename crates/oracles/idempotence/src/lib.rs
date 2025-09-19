use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use tf_oracles_core::{
    diff_values, err, ok, with_trace, DiffResult, Oracle, OracleCtx, OracleResult,
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
    pub iteration: Option<usize>,
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
    pub iteration: usize,
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
    let missing_value = Value::String(MISSING_VALUE.to_string());

    for idempotence_case in &input.cases {
        cases_checked += 1;
        let applications = canonicalize_applications(&idempotence_case.applications, ctx);
        if applications.len() <= 1 {
            continue;
        }
        let baseline = &applications[0];
        for candidate in applications.iter().skip(1) {
            applications_checked += 1;
            if let Some(diff) = diff_values(&baseline.value, &candidate.value, &missing_value) {
                mismatches.push(build_mismatch(idempotence_case, candidate.iteration, diff));
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

    let details = json!({ "mismatches": mismatches });
    let failure = err(FAILURE_CODE, "Repeated application diverged", Some(details));
    let trace = mismatches
        .iter()
        .take(5)
        .map(|mismatch| format!("case:{}:iteration:{}", mismatch.case, mismatch.iteration));
    with_trace(failure, trace).into()
}

fn canonicalize_applications(
    applications: &[IdempotenceApplication],
    ctx: &OracleCtx,
) -> Vec<CanonicalApplication> {
    applications
        .iter()
        .enumerate()
        .map(|(index, application)| CanonicalApplication {
            iteration: application.iteration.unwrap_or(index),
            value: ctx.canonicalize_value(application.value.clone()),
        })
        .collect()
}

#[derive(Debug, Clone)]
struct CanonicalApplication {
    iteration: usize,
    value: Value,
}

fn build_mismatch(
    case: &IdempotenceCase,
    iteration: usize,
    diff: DiffResult,
) -> IdempotenceMismatch {
    IdempotenceMismatch {
        case: case.name.clone(),
        seed: case.seed.clone(),
        iteration,
        pointer: diff.pointer,
        expected: diff.left,
        actual: diff.right,
    }
}
