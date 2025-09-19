use serde_json::{json, Value};
use tf_oracles_core::{Oracle, OracleCtx};
use tf_oracles_transport::{
    check_transport, TransportCase, TransportDrift, TransportInput, TransportOracle,
};

#[test]
fn accepts_json_values() {
    let ctx = OracleCtx::new("0xfeed").with_now(0);
    let oracle = TransportOracle::new();
    let input = TransportInput {
        cases: vec![TransportCase {
            name: "scalar".to_string(),
            seed: Some("0x01".to_string()),
            value: json!({ "value": [1, 2, 3] }),
            encoded: None,
        }],
    };

    let result = oracle.check(&input, &ctx);
    match result {
        tf_oracles_core::OracleResult::Success(success) => {
            assert_eq!(success.value.cases_checked, 1);
            assert_eq!(success.value.round_trips_checked, 1);
        }
        tf_oracles_core::OracleResult::Failure(_) => panic!("expected success"),
    }
}

#[test]
fn detects_missing_fields() {
    let ctx = OracleCtx::new("0xfeed").with_now(0);
    let input = TransportInput {
        cases: vec![TransportCase {
            name: "drop".to_string(),
            seed: Some("0x02".to_string()),
            value: json!({ "keep": true, "drop": 42 }),
            encoded: Some(Value::String("{\"keep\":true}".to_string())),
        }],
    };

    let result = check_transport(&input, &ctx);
    match result {
        tf_oracles_core::OracleResult::Failure(failure) => {
            assert_eq!(failure.error.code, "E_TRANSPORT_DRIFT");
            let details = failure.error.details.expect("details");
            let payload: serde_json::Value = details;
            let drifts: Vec<TransportDrift> =
                serde_json::from_value(payload.get("drifts").cloned().expect("drifts"))
                    .expect("drift array");
            assert_eq!(drifts.len(), 1);
            let drift = &drifts[0];
            assert_eq!(drift.pointer, "/drop");
            assert_eq!(drift.before, json!(42));
            assert_eq!(drift.after, json!("[missing]"));
        }
        tf_oracles_core::OracleResult::Success(_) => panic!("expected failure"),
    }
}

#[test]
fn flags_invalid_json() {
    let ctx = OracleCtx::new("0xfeed").with_now(0);
    let input = TransportInput {
        cases: vec![TransportCase {
            name: "invalid".to_string(),
            seed: Some("0x03".to_string()),
            value: json!({ "ok": true }),
            encoded: Some(Value::String("{ not json }".to_string())),
        }],
    };

    let result = check_transport(&input, &ctx);
    match result {
        tf_oracles_core::OracleResult::Failure(failure) => {
            assert_eq!(failure.error.code, "E_TRANSPORT_DECODE");
            let details = failure.error.details.expect("details");
            let payload: serde_json::Value = details;
            let drifts: Vec<TransportDrift> =
                serde_json::from_value(payload.get("drifts").cloned().expect("drifts"))
                    .expect("drift array");
            assert_eq!(drifts[0].pointer, "");
            assert_eq!(drifts[0].after, json!("[invalid-json]"));
        }
        tf_oracles_core::OracleResult::Success(_) => panic!("expected failure"),
    }
}

#[test]
fn reports_root_pointer_differences() {
    let ctx = OracleCtx::new("0xfeed").with_now(0);
    let input = TransportInput {
        cases: vec![TransportCase {
            name: "root".to_string(),
            seed: None,
            value: json!(1),
            encoded: Some(Value::String("2".to_string())),
        }],
    };

    let result = check_transport(&input, &ctx);
    match result {
        tf_oracles_core::OracleResult::Failure(failure) => {
            assert_eq!(failure.error.code, "E_TRANSPORT_DRIFT");
            let details = failure.error.details.expect("details");
            let payload: serde_json::Value = details;
            let drifts: Vec<TransportDrift> =
                serde_json::from_value(payload.get("drifts").cloned().expect("drifts"))
                    .expect("drift array");
            assert_eq!(drifts[0].pointer, "");
            assert_eq!(drifts[0].before, json!(1));
            assert_eq!(drifts[0].after, json!(2));
        }
        tf_oracles_core::OracleResult::Success(_) => panic!("expected failure"),
    }
}

#[test]
fn rejects_non_string_encoded() {
    let ctx = OracleCtx::new("0xfeed").with_now(0);
    let input = TransportInput {
        cases: vec![TransportCase {
            name: "type".to_string(),
            seed: None,
            value: json!({ "ok": true }),
            encoded: None,
        }],
    };

    let mut malformed = input.clone();
    malformed.cases[0].encoded = Some(Value::String(
        serde_json::to_string(&json!({ "ok": true })).unwrap(),
    ));
    let result = check_transport(&malformed, &ctx);
    assert!(matches!(result, tf_oracles_core::OracleResult::Success(_)));

    let mut wrong_type = input.clone();
    wrong_type.cases[0].encoded = Some(json!({ "raw": true }));
    let result = check_transport(&wrong_type, &ctx);
    match result {
        tf_oracles_core::OracleResult::Failure(failure) => {
            assert_eq!(failure.error.code, "E_TRANSPORT_SERIALIZE");
        }
        _ => panic!("expected serialization failure"),
    }

    let mut bad = input;
    bad.cases[0].encoded = Some(Value::String(String::new()));
    let result = check_transport(&bad, &ctx);
    match result {
        tf_oracles_core::OracleResult::Failure(failure) => {
            assert_eq!(failure.error.code, "E_TRANSPORT_DECODE");
        }
        _ => panic!("expected decode failure"),
    }
}
