use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use serde_json::Value;
use tf_oracles_core::{err, ok, with_trace, Oracle, OracleCtx, OracleResult};

const FAILURE_CODE: &str = "E_NON_DETERMINISTIC";

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeterminismRun {
    #[serde(rename = "runId")]
    pub run_id: String,
    #[serde(rename = "final")]
    pub final_state: Value,
    #[serde(default)]
    pub checkpoints: BTreeMap<String, Value>,
    #[serde(default)]
    pub note: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeterminismCase {
    pub name: String,
    pub seed: String,
    pub runs: Vec<DeterminismRun>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct DeterminismInput {
    pub cases: Vec<DeterminismCase>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct DeterminismReport {
    #[serde(rename = "casesChecked")]
    pub cases_checked: usize,
    #[serde(rename = "runsChecked")]
    pub runs_checked: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct CheckpointMismatch {
    pub checkpoint: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expected: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub actual: Option<Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct CaseMismatch {
    pub case: String,
    pub seed: String,
    pub run: String,
    pub mismatches: Vec<CheckpointMismatch>,
}

#[derive(Debug, Clone)]
struct CanonicalRun {
    run_id: String,
    final_state: Value,
    checkpoints: BTreeMap<String, Value>,
}

#[derive(Debug, Default)]
pub struct DeterminismOracle;

impl DeterminismOracle {
    pub fn new() -> Self {
        Self
    }
}

impl Oracle<DeterminismInput, DeterminismReport> for DeterminismOracle {
    fn check(&self, input: &DeterminismInput, ctx: &OracleCtx) -> OracleResult<DeterminismReport> {
        check_determinism(input, ctx)
    }
}

pub fn check_determinism(input: &DeterminismInput, ctx: &OracleCtx) -> OracleResult<DeterminismReport> {
    let mut cases_checked = 0usize;
    let mut runs_checked = 0usize;
    let mut mismatches: Vec<CaseMismatch> = Vec::new();

    for determinism_case in &input.cases {
        cases_checked += 1;
        let canonical_runs: Vec<CanonicalRun> = determinism_case
            .runs
            .iter()
            .map(|run| canonicalize_run(run, ctx))
            .collect();
        runs_checked += canonical_runs.len();

        if canonical_runs.len() <= 1 {
            continue;
        }

        let baseline = &canonical_runs[0];
        for candidate in canonical_runs.iter().skip(1) {
            let diffs = diff_runs(baseline, candidate);
            if !diffs.is_empty() {
                mismatches.push(CaseMismatch {
                    case: determinism_case.name.clone(),
                    seed: determinism_case.seed.clone(),
                    run: candidate.run_id.clone(),
                    mismatches: diffs,
                });
            }
        }
    }

    if mismatches.is_empty() {
        let report = DeterminismReport {
            cases_checked,
            runs_checked,
        };
        return ok(report, std::iter::empty::<&str>());
    }

    let details = serde_json::json!({ "mismatches": mismatches });
    let failure = err(FAILURE_CODE, "Runs diverged under identical seeds", Some(details));
    let trace = mismatches
        .iter()
        .take(5)
        .map(|case| format!("case:{}:run:{}", case.case, case.run));
    OracleResult::from(with_trace(failure, trace))
}

fn canonicalize_run(run: &DeterminismRun, ctx: &OracleCtx) -> CanonicalRun {
    let final_state = ctx.canonicalize_value(run.final_state.clone());
    let mut checkpoints = BTreeMap::new();
    for (key, value) in &run.checkpoints {
        checkpoints.insert(key.clone(), ctx.canonicalize_value(value.clone()));
    }
    CanonicalRun {
        run_id: run.run_id.clone(),
        final_state,
        checkpoints,
    }
}

fn diff_runs(baseline: &CanonicalRun, candidate: &CanonicalRun) -> Vec<CheckpointMismatch> {
    let mut mismatches = Vec::new();
    if baseline.final_state != candidate.final_state {
        mismatches.push(CheckpointMismatch {
            checkpoint: "final".to_string(),
            expected: Some(baseline.final_state.clone()),
            actual: Some(candidate.final_state.clone()),
        });
    }

    let mut keys = BTreeSet::new();
    keys.extend(baseline.checkpoints.keys().cloned());
    keys.extend(candidate.checkpoints.keys().cloned());

    for key in keys {
        let expected = baseline.checkpoints.get(&key).cloned();
        let actual = candidate.checkpoints.get(&key).cloned();
        if expected != actual {
            mismatches.push(CheckpointMismatch {
                checkpoint: key,
                expected,
                actual,
            });
        }
    }

    mismatches
}
