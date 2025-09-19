use serde_json::json;
use tf_oracles_core::{Oracle, OracleCtx};
use tf_oracles_idempotence::{
    check_idempotence, IdempotenceApplication, IdempotenceCase, IdempotenceInput,
    IdempotenceMismatch, IdempotenceOracle,
};

#[test]
fn accepts_equal_applications() {
    let ctx = OracleCtx::new("0xfeed").with_now(0);
    let oracle = IdempotenceOracle::new();
    let input = IdempotenceInput {
        cases: vec![IdempotenceCase {
            name: "case".to_string(),
            seed: Some("0x01".to_string()),
            applications: vec![
                application(0, json!({ "value": [1, 2, 3] })),
                application(1, json!({ "value": [1, 2, 3] })),
                application(2, json!({ "value": [1, 2, 3] })),
            ],
        }],
    };

    let result = oracle.check(&input, &ctx);
    match result {
        tf_oracles_core::OracleResult::Success(success) => {
            assert_eq!(success.value.cases_checked, 1);
            assert_eq!(success.value.applications_checked, 2);
        }
        tf_oracles_core::OracleResult::Failure(_) => panic!("expected success"),
    }
}

#[test]
fn detects_divergent_application() {
    let ctx = OracleCtx::new("0xfeed").with_now(0);
    let input = IdempotenceInput {
        cases: vec![IdempotenceCase {
            name: "drift".to_string(),
            seed: Some("0x02".to_string()),
            applications: vec![
                application(0, json!({ "nested": { "value": [1, 2, 3] } })),
                application(1, json!({ "nested": { "value": [1, 4, 3] } })),
            ],
        }],
    };

    let result = check_idempotence(&input, &ctx);
    match result {
        tf_oracles_core::OracleResult::Failure(failure) => {
            assert_eq!(failure.error.code, "E_NOT_IDEMPOTENT");
            let details = failure.error.details.expect("details");
            let payload: serde_json::Value = details;
            let mismatches: Vec<IdempotenceMismatch> =
                serde_json::from_value(payload.get("mismatches").cloned().expect("mismatches"))
                    .expect("mismatch array");
            assert_eq!(mismatches.len(), 1);
            assert_eq!(mismatches[0].pointer, "/nested/value/1");
        }
        tf_oracles_core::OracleResult::Success(_) => panic!("expected failure"),
    }
}

#[test]
fn reports_missing_field() {
    let ctx = OracleCtx::new("0xfeed").with_now(0);
    let input = IdempotenceInput {
        cases: vec![IdempotenceCase {
            name: "missing".to_string(),
            seed: None,
            applications: vec![
                application(0, json!({ "keep": true })),
                application(1, json!({ "keep": true, "extra": 42 })),
            ],
        }],
    };

    let result = check_idempotence(&input, &ctx);
    match result {
        tf_oracles_core::OracleResult::Failure(failure) => {
            let details = failure.error.details.expect("details");
            let payload: serde_json::Value = details;
            let mismatches: Vec<IdempotenceMismatch> =
                serde_json::from_value(payload.get("mismatches").cloned().expect("mismatches"))
                    .expect("mismatch array");
            let mismatch = mismatches.first().expect("first mismatch");
            assert_eq!(mismatch.pointer, "/extra");
            assert_eq!(mismatch.expected, json!("[missing]"));
            assert_eq!(mismatch.actual, json!(42));
        }
        tf_oracles_core::OracleResult::Success(_) => panic!("expected failure"),
    }
}

fn application(iteration: usize, value: serde_json::Value) -> IdempotenceApplication {
    IdempotenceApplication {
        iteration: Some(iteration),
        value,
    }
}
