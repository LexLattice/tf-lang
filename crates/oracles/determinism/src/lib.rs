use serde::{Deserialize, Serialize};
use serde_json::{json, Map, Value};
use tf_oracles_core::{err, ok, ErrorOptions, OracleCtx, OracleOutcome};

const ERR_INSUFFICIENT_RUNS: &str = "E_DETERMINISM_INSUFFICIENT_RUNS";
const ERR_CHECKPOINT_COUNT: &str = "E_DETERMINISM_CHECKPOINT_COUNT";
const ERR_CHECKPOINT_LABEL: &str = "E_DETERMINISM_CHECKPOINT_LABEL";
const ERR_CHECKPOINT_STATE: &str = "E_DETERMINISM_CHECKPOINT_STATE";
const ERR_FINAL_STATE: &str = "E_DETERMINISM_FINAL_STATE";

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct DeterminismCheckpoint {
    pub label: String,
    pub state: Value,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct DeterminismRun {
    pub runtime: String,
    #[serde(default)]
    pub checkpoints: Vec<DeterminismCheckpoint>,
    pub final_state: Value,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct DeterminismInput {
    pub runs: Vec<DeterminismRun>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct DeterminismReport {
    pub seed: String,
    pub runs: Vec<RunSummary>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct RunSummary {
    pub runtime: String,
    pub checkpoints: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct DeterminismDiff {
    pub path: String,
    pub left: Value,
    pub right: Value,
}

fn missing_marker() -> Value {
    let mut map = Map::new();
    map.insert("missing".to_string(), Value::Bool(true));
    Value::Object(map)
}

fn encode_token(token: &str) -> String {
    token.replace('~', "~0").replace('/', "~1")
}

fn join_path(base: &str, token: &str) -> String {
    let encoded = encode_token(token);
    if base.is_empty() {
        format!("/{}", encoded)
    } else {
        format!("{}/{}", base, encoded)
    }
}

fn diff_values(left: &Value, right: &Value, path: &str) -> Option<DeterminismDiff> {
    if left == right {
        return None;
    }

    match (left, right) {
        (Value::Array(a), Value::Array(b)) => {
            let max_len = a.len().max(b.len());
            for idx in 0..max_len {
                if idx >= a.len() {
                    return Some(DeterminismDiff {
                        path: join_path(path, &idx.to_string()),
                        left: missing_marker(),
                        right: b.get(idx).cloned().unwrap_or_else(missing_marker),
                    });
                }
                if idx >= b.len() {
                    return Some(DeterminismDiff {
                        path: join_path(path, &idx.to_string()),
                        left: a.get(idx).cloned().unwrap_or_else(missing_marker),
                        right: missing_marker(),
                    });
                }
                if let Some(diff) = diff_values(
                    &a[idx],
                    &b[idx],
                    &join_path(path, &idx.to_string()),
                ) {
                    return Some(diff);
                }
            }
            None
        }
        (Value::Object(a), Value::Object(b)) => {
            let mut keys: Vec<String> = a.keys().cloned().collect();
            for key in b.keys() {
                if !a.contains_key(key) {
                    keys.push(key.clone());
                }
            }
            keys.sort();
            keys.dedup();
            for key in keys {
                match (a.get(&key), b.get(&key)) {
                    (Some(l), Some(r)) => {
                        if let Some(diff) = diff_values(l, r, &join_path(path, &key)) {
                            return Some(diff);
                        }
                    }
                    (Some(l), None) => {
                        return Some(DeterminismDiff {
                            path: join_path(path, &key),
                            left: l.clone(),
                            right: missing_marker(),
                        });
                    }
                    (None, Some(r)) => {
                        return Some(DeterminismDiff {
                            path: join_path(path, &key),
                            left: missing_marker(),
                            right: r.clone(),
                        });
                    }
                    (None, None) => continue,
                }
            }
            None
        }
        _ => Some(DeterminismDiff {
            path: if path.is_empty() { "/".to_string() } else { path.to_string() },
            left: left.clone(),
            right: right.clone(),
        }),
    }
}

fn canonicalize_value(ctx: &OracleCtx, value: &Value) -> Value {
    ctx.canonicalize(value).unwrap_or_else(|_| value.clone())
}

fn canonicalize_detail(ctx: &OracleCtx, value: Value) -> Value {
    ctx.canonicalize(&value).unwrap_or(value)
}

fn build_error(
    code: &str,
    explain: &str,
    ctx: &OracleCtx,
    details: Value,
    trace: Vec<String>,
) -> OracleOutcome<DeterminismReport> {
    let mut options = ErrorOptions::default();
    options.details = Some(canonicalize_detail(ctx, details));
    options.trace = trace;
    OracleOutcome::from(err(code.to_string(), explain.to_string(), options))
}

pub fn check(input: DeterminismInput, ctx: &OracleCtx) -> OracleOutcome<DeterminismReport> {
    if input.runs.len() < 2 {
        return build_error(
            ERR_INSUFFICIENT_RUNS,
            "need at least two runs to compare",
            ctx,
            json!({ "runCount": input.runs.len() }),
            Vec::new(),
        );
    }

    let runs = input.runs;
    let baseline = &runs[0];
    let baseline_canonical: Vec<Value> = baseline
        .checkpoints
        .iter()
        .map(|cp| canonicalize_value(ctx, &cp.state))
        .collect();
    let baseline_final = canonicalize_value(ctx, &baseline.final_state);

    for candidate in runs.iter().skip(1) {
        let trace = vec![baseline.runtime.clone(), candidate.runtime.clone()];
        if baseline.checkpoints.len() != candidate.checkpoints.len() {
            return build_error(
                ERR_CHECKPOINT_COUNT,
                "checkpoint count mismatch",
                ctx,
                json!({
                    "baseline": baseline.checkpoints.len(),
                    "candidate": candidate.checkpoints.len(),
                    "runtimes": {
                        "baseline": baseline.runtime,
                        "candidate": candidate.runtime
                    }
                }),
                trace,
            );
        }

        for (idx, (base_cp, cand_cp)) in baseline
            .checkpoints
            .iter()
            .zip(candidate.checkpoints.iter())
            .enumerate()
        {
            if base_cp.label != cand_cp.label {
                return build_error(
                    ERR_CHECKPOINT_LABEL,
                    "checkpoint labels diverged",
                    ctx,
                    json!({
                        "index": idx,
                        "baseline": base_cp.label,
                        "candidate": cand_cp.label,
                    }),
                    trace.clone(),
                );
            }
            let candidate_canonical = canonicalize_value(ctx, &cand_cp.state);
            if baseline_canonical[idx] != candidate_canonical {
                let diff = diff_values(&baseline_canonical[idx], &candidate_canonical, "")
                    .unwrap_or_else(|| DeterminismDiff {
                        path: "/".to_string(),
                        left: baseline_canonical[idx].clone(),
                        right: candidate_canonical.clone(),
                    });
                return build_error(
                    ERR_CHECKPOINT_STATE,
                    "checkpoint states diverged",
                    ctx,
                    json!({
                        "index": idx,
                        "label": base_cp.label,
                        "diff": diff,
                    }),
                    trace.clone(),
                );
            }
        }

        let candidate_final = canonicalize_value(ctx, &candidate.final_state);
        if baseline_final != candidate_final {
            let diff = diff_values(&baseline_final, &candidate_final, "")
                .unwrap_or_else(|| DeterminismDiff {
                    path: "/".to_string(),
                    left: baseline_final.clone(),
                    right: candidate_final.clone(),
                });
            return build_error(
                ERR_FINAL_STATE,
                "final state diverged",
                ctx,
                json!({ "diff": diff }),
                trace,
            );
        }
    }

    let report = DeterminismReport {
        seed: ctx.seed.clone(),
        runs: runs
            .iter()
            .map(|run| RunSummary {
                runtime: run.runtime.clone(),
                checkpoints: run.checkpoints.len(),
            })
            .collect(),
    };
    OracleOutcome::from(ok(report))
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    const HAPPY: &str = include_str!("../../../../packages/oracles/determinism/fixtures/happy.json");
    const FINAL_MISMATCH: &str = include_str!(
        "../../../../packages/oracles/determinism/fixtures/final-mismatch.json"
    );

    const RUNTIMES: [&str; 3] = ["ts", "rs", "wasm"];

    use proptest::test_runner::{Config, RngSeed, TestRunner};

    fn json_value_strategy(depth: u32) -> BoxedStrategy<Value> {
        let leaf = prop_oneof![
            Just(Value::Null),
            any::<bool>().prop_map(Value::Bool),
            any::<i64>().prop_map(|v| Value::Number(v.into())),
            prop::string::string_regex("[a-z0-9_-]{0,6}")
                .unwrap()
                .prop_map(Value::String),
        ];
        if depth >= 2 {
            return leaf.boxed();
        }
        let array = prop::collection::vec(json_value_strategy(depth + 1), 0..4)
            .prop_map(Value::Array);
        let object = prop::collection::vec(
            (
                prop::string::string_regex("[a-z0-9_-]{1,6}").unwrap(),
                json_value_strategy(depth + 1),
            ),
            0..4,
        )
        .prop_map(|entries| {
            let mut map = Map::new();
            for (k, v) in entries {
                map.insert(k, v);
            }
            Value::Object(map)
        });
        prop_oneof![leaf, array, object].boxed()
    }

    fn base_strategy() -> impl Strategy<Value = (Vec<(String, Value)>, Value)> {
        (
            prop::collection::vec(
                (
                    prop::string::string_regex("[a-z0-9_-]{1,6}").unwrap(),
                    json_value_strategy(0),
                ),
                0..4,
            ),
            json_value_strategy(0),
        )
    }

    fn identical_strategy() -> impl Strategy<Value = DeterminismInput> {
        base_strategy().prop_flat_map(|(checkpoints, final_state)| {
            let runs_strategy = prop::collection::vec(
                prop::sample::select(&RUNTIMES),
                2..=RUNTIMES.len(),
            )
            .prop_map(move |names| {
                let runs = names
                    .into_iter()
                    .map(|name| DeterminismRun {
                        runtime: name.to_string(),
                        checkpoints: checkpoints
                            .iter()
                            .map(|(label, state)| DeterminismCheckpoint {
                                label: label.clone(),
                                state: state.clone(),
                            })
                            .collect(),
                        final_state: final_state.clone(),
                    })
                    .collect();
                DeterminismInput { runs }
            });
            runs_strategy
        })
    }

    fn mutated_strategy() -> impl Strategy<Value = DeterminismInput> {
        base_strategy().prop_flat_map(|(checkpoints, final_state)| {
            prop::collection::vec(prop::sample::select(&RUNTIMES), 2..=RUNTIMES.len())
                .prop_map(move |names| {
                    let mut runs: Vec<DeterminismRun> = names
                        .into_iter()
                        .map(|name| DeterminismRun {
                            runtime: name.to_string(),
                            checkpoints: checkpoints
                                .iter()
                                .map(|(label, state)| DeterminismCheckpoint {
                                    label: label.clone(),
                                    state: state.clone(),
                                })
                                .collect(),
                            final_state: final_state.clone(),
                        })
                        .collect();
                    if let Some(last) = runs.last_mut() {
                        if !last.checkpoints.is_empty() {
                            let target = last.checkpoints.len() - 1;
                            let original = last.checkpoints[target].state.clone();
                            last.checkpoints[target].state = json!({
                                "mutated": true,
                                "original": original
                            });
                        } else {
                            let original = last.final_state.clone();
                            last.final_state = json!({
                                "mutated": true,
                                "original": original
                            });
                        }
                    }
                    DeterminismInput { runs }
                })
        })
    }

    #[test]
    fn accepts_fixture() {
        let input: DeterminismInput = serde_json::from_str(HAPPY).expect("fixture");
        let result = check(input, &OracleCtx::new("0x6f2a7c9bbabc1234", 0));
        assert!(matches!(result, OracleOutcome::Ok(_)));
    }

    #[test]
    fn rejects_final_mismatch() {
        let input: DeterminismInput = serde_json::from_str(FINAL_MISMATCH).expect("fixture");
        let result = check(input, &OracleCtx::new("0x6f2a7c9bbabc1234", 0));
        assert!(matches!(result, OracleOutcome::Err(_)));
    }

    #[test]
    fn proptest_identical_runs() {
        const SEED: u64 = 0x6f2a7c9bbabc1234;
        let mut runner = TestRunner::new(Config {
            cases: 40,
            rng_seed: RngSeed::Fixed(SEED),
            ..Config::default()
        });
        runner
            .run(&identical_strategy(), |input| {
                let ctx = OracleCtx::new("0x6f2a7c9bbabc1234", 0);
                let first = check(input.clone(), &ctx);
                let second = check(input, &ctx);
                prop_assert!(matches!(first, OracleOutcome::Ok(_)));
                prop_assert_eq!(first, second);
                Ok(())
            })
            .expect("proptest identical runs");
    }

    #[test]
    fn proptest_mutated_runs() {
        const SEED: u64 = 0x5eadbeefcafebabe;
        let mut runner = TestRunner::new(Config {
            cases: 40,
            rng_seed: RngSeed::Fixed(SEED),
            ..Config::default()
        });
        runner
            .run(&mutated_strategy(), |input| {
                let ctx = OracleCtx::new("0x5eadbeefcafebabe", 0);
                let first = check(input.clone(), &ctx);
                let second = check(input, &ctx);
                prop_assert!(matches!(first, OracleOutcome::Err(_)));
                prop_assert_eq!(first, second);
                Ok(())
            })
            .expect("proptest mutated runs");
    }
}
