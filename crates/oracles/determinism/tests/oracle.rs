use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;
use std::sync::OnceLock;

use proptest::prelude::*;
use proptest::test_runner::{
    Config as ProptestConfig, RngAlgorithm, TestCaseError, TestRng, TestRunner,
};
use serde::Deserialize;
use serde_json::{Number, Value};
use tf_oracles_core::{Oracle, OracleCtx, OracleResult};
use tf_oracles_determinism::{
    check_determinism, CaseMismatch, DeterminismCase, DeterminismInput, DeterminismOracle,
    DeterminismRun,
};

#[test]
fn identical_runs_pass_property() {
    let seeds = seeds();
    let mut config = ProptestConfig::with_cases(64);
    config.failure_persistence = None;
    let rng = TestRng::from_seed(RngAlgorithm::default(), &seeds.pass);
    let mut runner = TestRunner::new_with_rng(config, rng);

    runner
        .run(
            &(run_template_strategy(), run_ids_strategy()),
            |(template, run_ids)| {
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
                        return Err(TestCaseError::fail(format!(
                            "expected success, got {:?}",
                            failure
                        )));
                    }
                }

                Ok(())
            },
        )
        .unwrap();
}

#[test]
fn drift_is_detected_property() {
    let seeds = seeds();
    let mut config = ProptestConfig::with_cases(48);
    config.failure_persistence = None;
    let rng = TestRng::from_seed(RngAlgorithm::default(), &seeds.fail);
    let mut runner = TestRunner::new_with_rng(config, rng);

    runner
        .run(
            &(run_template_strategy(), run_ids_strategy(), any::<bool>()),
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
                            last.checkpoints.insert(
                                "__mut__".to_string(),
                                perturb_value(&template.final_state),
                            );
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

#[test]
fn fixtures_match_expectations() {
    let ctx = OracleCtx::new("0xfeed").with_now(0);

    for fixture in fixtures_from_disk() {
        let expected = &fixture.data.expect;
        assert_eq!(
            fixture.data.input.cases.len(),
            expected.cases_checked,
            "fixture {} case count mismatch",
            fixture.name
        );
        assert_eq!(
            count_runs(&fixture.data.input),
            expected.runs_checked,
            "fixture {} run count mismatch",
            fixture.name
        );

        match check_determinism(&fixture.data.input, &ctx) {
            OracleResult::Success(success) => {
                assert!(
                    expected.ok,
                    "fixture {} expected failure but succeeded",
                    fixture.name
                );
                assert_eq!(
                    success.value.cases_checked, expected.cases_checked,
                    "fixture {} cases checked mismatch",
                    fixture.name
                );
                assert_eq!(
                    success.value.runs_checked, expected.runs_checked,
                    "fixture {} runs checked mismatch",
                    fixture.name
                );
            }
            OracleResult::Failure(failure) => {
                assert!(
                    !expected.ok,
                    "fixture {} expected success but failed",
                    fixture.name
                );
                assert_eq!(
                    failure.error.code, "E_NON_DETERMINISTIC",
                    "fixture {} failure code",
                    fixture.name
                );

                let mismatches_value = failure
                    .error
                    .details
                    .as_ref()
                    .and_then(|details| details.get("mismatches"))
                    .cloned()
                    .unwrap_or_else(|| Value::Array(Vec::new()));
                let mismatches: Vec<CaseMismatch> = serde_json::from_value(mismatches_value)
                    .unwrap_or_else(|err| {
                        panic!("fixture {} mismatch parse error: {err}", fixture.name)
                    });

                assert_eq!(
                    mismatches.len(),
                    expected.mismatches.len(),
                    "fixture {} mismatch count",
                    fixture.name
                );

                for expected_mismatch in &expected.mismatches {
                    let actual = mismatches
                        .iter()
                        .find(|entry| {
                            entry.case == expected_mismatch.case
                                && entry.run == expected_mismatch.run
                        })
                        .unwrap_or_else(|| {
                            panic!(
                                "fixture {} missing mismatch for case {} run {}",
                                fixture.name, expected_mismatch.case, expected_mismatch.run
                            )
                        });

                    assert_eq!(
                        actual.seed, expected_mismatch.seed,
                        "fixture {} seed mismatch for case {} run {}",
                        fixture.name, expected_mismatch.case, expected_mismatch.run
                    );

                    let mut actual_checkpoints: Vec<&str> = actual
                        .mismatches
                        .iter()
                        .map(|entry| entry.checkpoint.as_str())
                        .collect();
                    actual_checkpoints.sort();
                    let mut expected_checkpoints: Vec<&str> = expected_mismatch
                        .checkpoints
                        .iter()
                        .map(String::as_str)
                        .collect();
                    expected_checkpoints.sort();

                    assert_eq!(
                        actual_checkpoints, expected_checkpoints,
                        "fixture {} checkpoint mismatch for case {} run {}",
                        fixture.name, expected_mismatch.case, expected_mismatch.run
                    );
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
struct RunTemplate {
    final_state: Value,
    checkpoints: BTreeMap<String, Value>,
}

fn run_template_strategy() -> impl Strategy<Value = RunTemplate> {
    (json_value_strategy(), checkpoints_strategy()).prop_map(|(final_state, checkpoints)| {
        RunTemplate {
            final_state,
            checkpoints,
        }
    })
}

fn run_ids_strategy() -> impl Strategy<Value = Vec<String>> {
    prop::collection::btree_set(string_strategy(), 2..5).prop_map(|set| set.into_iter().collect())
}

fn checkpoints_strategy() -> impl Strategy<Value = BTreeMap<String, Value>> {
    prop::collection::btree_map(string_strategy(), json_value_strategy(), 0..4)
}

fn string_strategy() -> impl Strategy<Value = String> {
    prop::collection::vec(prop::char::range('a', 'z'), 1..6)
        .prop_map(|chars| chars.into_iter().collect())
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

#[derive(Debug)]
struct Seeds {
    pass: [u8; 32],
    fail: [u8; 32],
}

fn seeds() -> &'static Seeds {
    static CACHE: OnceLock<Seeds> = OnceLock::new();
    CACHE.get_or_init(load_seeds_from_disk)
}

fn load_seeds_from_disk() -> Seeds {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = manifest.join("tests").join("seeds.json");
    let raw = fs::read_to_string(&path).expect("read seeds fixture");
    let parsed: SeedsFile = serde_json::from_str(&raw).expect("parse seeds fixture");
    Seeds {
        pass: parse_seed(&parsed.rust.pass_property),
        fail: parse_seed(&parsed.rust.fail_property),
    }
}

fn parse_seed(value: &str) -> [u8; 32] {
    let hex = value.strip_prefix("0x").unwrap_or(value);
    assert!(hex.len() == 64, "seed must encode 32 bytes");
    let mut bytes = [0u8; 32];
    for (index, chunk) in hex.as_bytes().chunks(2).enumerate() {
        let text = std::str::from_utf8(chunk).expect("seed chunk utf8");
        bytes[index] = u8::from_str_radix(text, 16)
            .unwrap_or_else(|err| panic!("invalid seed byte {text}: {err}"));
    }
    bytes
}

fn count_runs(input: &DeterminismInput) -> usize {
    input.cases.iter().map(|case| case.runs.len()).sum()
}

#[derive(Debug, Deserialize)]
struct SeedsFile {
    rust: RuntimeSeeds,
}

#[derive(Debug, Deserialize)]
struct RuntimeSeeds {
    #[serde(rename = "passProperty")]
    pass_property: String,
    #[serde(rename = "failProperty")]
    fail_property: String,
}

#[derive(Debug, Deserialize)]
#[allow(dead_code)]
struct FixtureFile {
    description: String,
    input: DeterminismInput,
    expect: FixtureExpectation,
}

#[derive(Debug, Deserialize)]
struct FixtureExpectation {
    ok: bool,
    #[serde(rename = "casesChecked")]
    cases_checked: usize,
    #[serde(rename = "runsChecked")]
    runs_checked: usize,
    #[serde(default)]
    mismatches: Vec<FixtureMismatchExpectation>,
}

#[derive(Debug, Deserialize)]
struct FixtureMismatchExpectation {
    case: String,
    seed: String,
    run: String,
    #[serde(default)]
    checkpoints: Vec<String>,
}

struct LoadedFixture {
    name: String,
    data: FixtureFile,
}

fn fixtures_from_disk() -> Vec<LoadedFixture> {
    let fixtures_path = repository_root().join("packages/oracles/determinism/fixtures");
    let mut fixtures = Vec::new();
    for entry in fs::read_dir(&fixtures_path).expect("read fixtures directory") {
        let entry = entry.expect("read fixture entry");
        let file_type = entry.file_type().expect("fixture entry type");
        if !file_type.is_file() {
            continue;
        }
        if entry.path().extension().and_then(|ext| ext.to_str()) != Some("json") {
            continue;
        }
        let raw = fs::read_to_string(entry.path()).expect("read fixture file");
        let data: FixtureFile = serde_json::from_str(&raw).expect("parse fixture json");
        let name = entry.file_name().to_string_lossy().into_owned();
        fixtures.push(LoadedFixture { name, data });
    }
    fixtures.sort_by(|a, b| a.name.cmp(&b.name));
    fixtures
}

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|path| path.parent())
        .and_then(|path| path.parent())
        .expect("repository root")
        .to_path_buf()
}
