use serde_json::json;
use tf_oracles_conservation::{
    check_conservation, ConservationInput, ConservationOracle, ConservationViolation,
};
use tf_oracles_core::{Oracle, OracleCtx};

#[test]
fn accepts_balanced_snapshots() {
    let ctx = OracleCtx::new("0xfeed").with_now(0);
    let oracle = ConservationOracle::new();
    let input = ConservationInput {
        keys: vec!["records".to_string(), "alerts".to_string()],
        before: json!({ "records": 10, "alerts": 2 }),
        after: json!({ "records": 10, "alerts": 2 }),
    };

    let result = oracle.check(&input, &ctx);
    match result {
        tf_oracles_core::OracleResult::Success(success) => {
            assert_eq!(success.value.keys_checked, 2);
        }
        tf_oracles_core::OracleResult::Failure(_) => panic!("expected success"),
    }
}

#[test]
fn reports_differences() {
    let ctx = OracleCtx::new("0xfeed").with_now(0);
    let input = ConservationInput {
        keys: vec![],
        before: json!({ "records": 5, "alerts": 2 }),
        after: json!({ "records": 6, "alerts": 2 }),
    };

    let result = check_conservation(&input, &ctx);
    match result {
        tf_oracles_core::OracleResult::Failure(failure) => {
            assert_eq!(failure.error.code, "E_NOT_CONSERVED");
            let details = failure.error.details.expect("details");
            let payload: serde_json::Value = details;
            let violations: Vec<ConservationViolation> =
                serde_json::from_value(payload.get("violations").cloned().expect("violations"))
                    .expect("violation array");
            assert_eq!(violations.len(), 1);
            let violation = &violations[0];
            assert_eq!(violation.key, "records");
            assert_eq!(violation.before, json!(5));
            assert_eq!(violation.after, json!(6));
            assert_eq!(violation.delta, Some(1.0));
        }
        tf_oracles_core::OracleResult::Success(_) => panic!("expected failure"),
    }
}

#[test]
fn respects_declared_keys() {
    let ctx = OracleCtx::new("0xfeed").with_now(0);
    let input = ConservationInput {
        keys: vec!["alerts".to_string()],
        before: json!({ "records": 5, "alerts": 2 }),
        after: json!({ "records": 6, "alerts": 2, "extra": 9 }),
    };

    let result = check_conservation(&input, &ctx);
    match result {
        tf_oracles_core::OracleResult::Success(success) => {
            assert_eq!(success.value.keys_checked, 1);
        }
        tf_oracles_core::OracleResult::Failure(_) => panic!("expected success"),
    }
}
