
use std::collections::BTreeMap;

use proptest::prelude::*;
use proptest::test_runner::{Config as ProptestConfig, RngAlgorithm, TestCaseError, TestRng, TestRunner};
use serde_json::{Number, Value};
use tf_oracles_core::{Oracle, OracleCtx, OracleResult};
use tf_oracles_determinism::{check_determinism, DeterminismCase, DeterminismInput, DeterminismOracle, DeterminismRun};

const PASS_SEED: [u8; 32] = *b"determinism-pass-seed-0000000000";
const FAIL_SEED: [u8; 32] = *b"determinism-fail-seed-1111111111";

#[test]
fn identical_runs_pass_property() {
    let mut config = ProptestConfig::with_cases(64);
    config.failure_persistence = None;
    let rng = TestRng::from_seed(RngAlgorithm::default(), &PASS_SEED);
    let mut runner = TestRunner::new_with_rng(config, rng);

    runner
        .run(&(run_template_strategy(), run_ids_strategy()), |(template, run_ids)| {
            let runs = run_ids
                .iter()
                .map(|run_id| DeterminismRun {
                    run_id: run_id.clone(),
                    final_state: template.final_state.clone(),
                    checkpoints: template.checkpoints.clone(),
                    note: None,
                })
                .collect::<Vec<_>>();

            let input = DeterminismInput {
                cases: vec![DeterminismCase {
                    name: "case".to_string(),
                    seed: "0x01".to_string(),
                    runs,
                }],
            };

            let ctx = OracleCtx::new("0xfeed").with_now(0);
            match check_determinism(&input, &ctx) {
                OracleResult::Success(success) => {
                    prop_assert_eq!(success.value.cases_checked, 1);
                    prop_assert_eq!(success.value.runs_checked, input.cases[0].runs.len());
                }
                OracleResult::Failure(failure) => {
                    return Err(TestCaseError::fail(format!("expected success, got {:?}", failure)));
                }
            }

            Ok(())
        })
        .unwrap();
}

#[test]
fn drift_is_detected_property() {
    let mut config = ProptestConfig::with_cases(48);
    config.failure_persistence = None;
    let rng = TestRng::from_seed(RngAlgorithm::default(), &FAIL_SEED);
    let mut runner = TestRunner::new_with_rng(config, rng);

    runner
        .run(
            &(
                run_template_strategy(),
                run_ids_strategy(),
                any::<bool>(),
            ),
            |(template, run_ids, mutate_checkpoint)| {
                let baseline_runs: Vec<DeterminismRun> = run_ids
                    .iter()
                    .map(|run_id| DeterminismRun {
                        run_id: run_id.clone(),
                        final_state: template.final_state.clone(),
                        checkpoints: template.checkpoints.clone(),
                        note: None,
                    })
                    .collect();

                let mut mutated_runs = baseline_runs.clone();
                if let Some(last) = mutated_runs.last_mut() {
                    if mutate_checkpoint {
                        if let Some(first_key) = last.checkpoints.keys().next().cloned() {
                            last.checkpoints
                                .insert(first_key, perturb_value(&template.final_state));
                        } else {
                            last.checkpoints
                                .insert("__mut__".to_string(), perturb_value(&template.final_state));
                        }
                    } else {
                        last.final_state = perturb_value(&last.final_state);
                    }
                }

                let input = DeterminismInput {
                    cases: vec![DeterminismCase {
                        name: "case".to_string(),
                        seed: "0x02".to_string(),
                        runs: mutated_runs,
                    }],
                };

                let ctx = OracleCtx::new("0xfeed").with_now(0);
                match check_determinism(&input, &ctx) {
                    OracleResult::Failure(failure) => {
                        prop_assert_eq!(failure.error.code, "E_NON_DETERMINISTIC");
                    }
                    OracleResult::Success(success) => {
                        return Err(TestCaseError::fail(format!(
                            "expected failure, got {:?}",
                            success.value
                        )));
                    }
                }

                Ok(())
            },
        )
        .unwrap();
}

#[test]
fn ordering_is_ignored() {
    let oracle = DeterminismOracle::new();
    let ctx = OracleCtx::new("0xfeed").with_now(0);
    let input = DeterminismInput {
        cases: vec![DeterminismCase {
            name: "ordering".to_string(),
            seed: "0x03".to_string(),
            runs: vec![
                DeterminismRun {
                    run_id: "A".to_string(),
                    final_state: serde_json::json!({"b": 1, "a": 2}),
                    checkpoints: vec![("snap".to_string(), serde_json::json!({"z": 1, "x": 2}))]
                        .into_iter()
                        .collect(),
                    note: None,
                },
                DeterminismRun {
                    run_id: "B".to_string(),
                    final_state: serde_json::json!({"a": 2, "b": 1}),
                    checkpoints: vec![("snap".to_string(), serde_json::json!({"x": 2, "z": 1}))]
                        .into_iter()
                        .collect(),
                    note: None,
                },
            ],
        }],
    };

    match oracle.check(&input, &ctx) {
        OracleResult::Success(report) => {
            assert_eq!(report.value.cases_checked, 1);
        }
        OracleResult::Failure(failure) => panic!("unexpected failure: {:?}", failure),
    }
}

#[derive(Clone, Debug)]
struct RunTemplate {
    final_state: Value,
    checkpoints: BTreeMap<String, Value>,
}

fn run_template_strategy() -> impl Strategy<Value = RunTemplate> {
    (json_value_strategy(), checkpoints_strategy()).prop_map(|(final_state, checkpoints)| RunTemplate {
        final_state,
        checkpoints,
    })
}

fn run_ids_strategy() -> impl Strategy<Value = Vec<String>> {
    prop::collection::btree_set(string_strategy(), 2..5).prop_map(|set| set.into_iter().collect())
}

fn checkpoints_strategy() -> impl Strategy<Value = BTreeMap<String, Value>> {
    prop::collection::btree_map(string_strategy(), json_value_strategy(), 0..4)
}

fn string_strategy() -> impl Strategy<Value = String> {
    prop::collection::vec(prop::char::range('a', 'z'), 1..6).prop_map(|chars| chars.into_iter().collect())
}

fn json_value_strategy() -> impl Strategy<Value = Value> {
    let leaf = prop_oneof![
        Just(Value::Null),
        any::<bool>().prop_map(Value::Bool),
        any::<i64>().prop_map(|v| Value::Number(Number::from(v))),
        finite_f64().prop_map(|v| match Number::from_f64(v) {
            Some(num) => Value::Number(num),
            None => Value::String(format!("{v}")),
        }),
        string_strategy().prop_map(Value::String),
    ];

    leaf.prop_recursive(3, 12, 3, |inner| {
        prop_oneof![
            prop::collection::vec(inner.clone(), 0..3).prop_map(Value::Array),
            prop::collection::btree_map(string_strategy(), inner, 0..3)
                .prop_map(|map| Value::Object(map.into_iter().collect())),
        ]
    })
}

fn finite_f64() -> impl Strategy<Value = f64> {
    any::<f64>().prop_filter("finite", |v| v.is_finite())
}

fn perturb_value(value: &Value) -> Value {
    match value {
        Value::Number(num) => {
            if let Some(i) = num.as_i64() {
                Value::Number(Number::from(i + 1))
            } else if let Some(u) = num.as_u64() {
                Value::Number(Number::from(u + 1))
            } else if let Some(f) = num.as_f64() {
                match Number::from_f64(f + 1.0) {
                    Some(next) => Value::Number(next),
                    None => Value::String(format!("{}", f + 1.0)),
                }
            } else {
                Value::String("__mutated__".to_string())
            }
        }
        Value::String(text) => Value::String(format!("{text}__mutated")),
        Value::Bool(flag) => Value::Bool(!flag),
        Value::Array(values) => {
            let mut mutated = values.clone();
            mutated.push(Value::String("__mutated__".to_string()));
            Value::Array(mutated)
        }
        Value::Object(map) => {
            let mut mutated = map.clone();
            mutated.insert("__mutated__".to_string(), Value::Bool(true));
            Value::Object(mutated)
        }
        Value::Null => Value::String("__mutated__".to_string()),
    }
}
