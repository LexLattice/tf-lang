use serde_json::json;
use tf_oracles_core::{Oracle, OracleCtx, OracleResult};
use tf_oracles_transport::{
    check_transport, TransportCase, TransportDrift, TransportInput, TransportOracle,
};

#[test]
fn accepts_round_trippable_values() {
    let ctx = OracleCtx::new("0xfeed");
    let input = TransportInput {
        cases: vec![TransportCase {
            name: "round".to_string(),
            seed: Some("0x01".to_string()),
            value: json!({ "values": [1, 2, 3], "note": "ok" }),
            encoded: None,
        }],
    };

    let oracle = TransportOracle::new();
    let result = oracle.check(&input, &ctx);
    let success = match result {
        OracleResult::Success(success) => success,
        other => panic!("unexpected failure: {other:?}"),
    };
    assert_eq!(success.value.cases_checked, 1);
    assert_eq!(success.value.round_trips_checked, 1);
}

#[test]
fn detects_drift_when_encoded_differs() {
    let ctx = OracleCtx::new("0xfeed");
    let input = TransportInput {
        cases: vec![TransportCase {
            name: "drift".to_string(),
            seed: Some("0x02".to_string()),
            value: json!({ "keep": true, "drop": false }),
            encoded: Some("{\"keep\":true}".to_string()),
        }],
    };

    let result = check_transport(&input, &ctx);
    let failure = match result {
        OracleResult::Failure(failure) => failure,
        other => panic!("unexpected success: {other:?}"),
    };
    let details_json = failure.error.details.expect("details");
    let drifts_value = details_json
        .get("drifts")
        .cloned()
        .unwrap_or_else(|| json!([]));
    let details: Vec<TransportDrift> = serde_json::from_value(drifts_value).unwrap();
    assert_eq!(details.len(), 1);
    assert_eq!(details[0].pointer, "/drop");
    assert_eq!(details[0].after, json!("[missing]"));
}

#[test]
fn flags_invalid_encoded_payloads() {
    let ctx = OracleCtx::new("0xfeed");
    let input = TransportInput {
        cases: vec![TransportCase {
            name: "invalid".to_string(),
            seed: Some("0x03".to_string()),
            value: json!({ "keep": true }),
            encoded: Some("{ not json }".to_string()),
        }],
    };

    let result = check_transport(&input, &ctx);
    let failure = match result {
        OracleResult::Failure(failure) => failure,
        other => panic!("unexpected success: {other:?}"),
    };
    let details_json = failure.error.details.expect("details");
    let drifts_value = details_json
        .get("drifts")
        .cloned()
        .unwrap_or_else(|| json!([]));
    let details: Vec<TransportDrift> = serde_json::from_value(drifts_value).unwrap();
    assert_eq!(details[0].pointer, "");
    assert_eq!(details[0].after, json!("[invalid-json]"));
    assert_eq!(
        details[0].error.as_ref().map(|error| error.code.as_str()),
        Some("E_TRANSPORT_DECODE")
    );
}
