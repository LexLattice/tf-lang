use serde_json::json;
use tf_oracles_core::{Oracle, OracleCtx, OracleResult};
use tf_oracles_idempotence::{
    check_idempotence, IdempotenceApplication, IdempotenceCase, IdempotenceInput,
    IdempotenceMismatch, IdempotenceOracle,
};

#[test]
fn passes_for_identical_applications() {
    let ctx = OracleCtx::new("0xfeed");
    let input = IdempotenceInput {
        cases: vec![IdempotenceCase {
            name: "case".to_string(),
            seed: Some("0x01".to_string()),
            applications: vec![
                IdempotenceApplication {
                    iteration: Some(0),
                    value: json!({ "values": [1, 2, 3] }),
                },
                IdempotenceApplication {
                    iteration: Some(1),
                    value: json!({ "values": [1, 2, 3] }),
                },
            ],
        }],
    };

    let oracle = IdempotenceOracle::new();
    let result = oracle.check(&input, &ctx);
    let success = match result {
        OracleResult::Success(success) => success,
        other => panic!("unexpected failure: {other:?}"),
    };
    assert_eq!(success.value.cases_checked, 1);
    assert_eq!(success.value.applications_checked, 1);
}

#[test]
fn reports_pointer_for_nested_drift() {
    let ctx = OracleCtx::new("0xfeed");
    let input = IdempotenceInput {
        cases: vec![IdempotenceCase {
            name: "drift".to_string(),
            seed: Some("0x02".to_string()),
            applications: vec![
                IdempotenceApplication {
                    iteration: Some(0),
                    value: json!({ "nested": { "value": [1, 2, 3] } }),
                },
                IdempotenceApplication {
                    iteration: Some(1),
                    value: json!({ "nested": { "value": [1, 4, 3] } }),
                },
            ],
        }],
    };

    let result = check_idempotence(&input, &ctx);
    let failure = match result {
        OracleResult::Failure(failure) => failure,
        other => panic!("unexpected success: {other:?}"),
    };
    let details_json = failure.error.details.expect("details");
    let mismatches_value = details_json
        .get("mismatches")
        .cloned()
        .unwrap_or_else(|| json!([]));
    let details: Vec<IdempotenceMismatch> = serde_json::from_value(mismatches_value).unwrap();
    assert_eq!(details.len(), 1);
    assert_eq!(details[0].pointer, "/nested/value/1");
}

#[test]
fn uses_root_pointer_for_top_level_diff() {
    let ctx = OracleCtx::new("0xfeed");
    let input = IdempotenceInput {
        cases: vec![IdempotenceCase {
            name: "root".to_string(),
            seed: Some("0x03".to_string()),
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

    let result = check_idempotence(&input, &ctx);
    let failure = match result {
        OracleResult::Failure(failure) => failure,
        other => panic!("unexpected success: {other:?}"),
    };
    let details_json = failure.error.details.expect("details");
    let mismatches_value = details_json
        .get("mismatches")
        .cloned()
        .unwrap_or_else(|| json!([]));
    let details: Vec<IdempotenceMismatch> = serde_json::from_value(mismatches_value).unwrap();
    assert_eq!(details[0].pointer, "");
    assert_eq!(details[0].expected, json!(1));
    assert_eq!(details[0].actual, json!(2));
}
