use std::collections::BTreeMap;

use serde_json::json;
use tf_oracles_conservation::{
    check_conservation, ConservationInput, ConservationOracle, ConservationViolation,
};
use tf_oracles_core::{Oracle, OracleCtx, OracleResult};

#[test]
fn passes_when_snapshots_match() {
    let ctx = OracleCtx::new("0xfeed");
    let mut before = BTreeMap::new();
    before.insert("records".to_string(), json!(4));
    before.insert("warnings".to_string(), json!(1));
    before.insert("alerts".to_string(), json!(0));
    let after = before.clone();

    let input = ConservationInput {
        version: None,
        subject: None,
        keys: Some(vec!["records".into(), "warnings".into(), "alerts".into()]),
        before: Some(before),
        after: Some(after),
    };

    let oracle = ConservationOracle::new();
    let result = oracle.check(&input, &ctx);
    let success = match result {
        OracleResult::Success(success) => success,
        other => panic!("unexpected failure: {other:?}"),
    };
    assert_eq!(success.value.keys_checked, 3);
}

#[test]
fn reports_missing_keys() {
    let ctx = OracleCtx::new("0xfeed");
    let mut before = BTreeMap::new();
    before.insert("records".to_string(), json!(5));
    let mut after = BTreeMap::new();
    after.insert("warnings".to_string(), json!(5));

    let input = ConservationInput {
        version: None,
        subject: None,
        keys: Some(vec!["records".into(), "warnings".into()]),
        before: Some(before),
        after: Some(after),
    };

    let result = check_conservation(&input, &ctx);
    let failure = match result {
        OracleResult::Failure(failure) => failure,
        other => panic!("unexpected success: {other:?}"),
    };
    let details_json = failure.error.details.expect("details");
    let violations_value = details_json
        .get("violations")
        .cloned()
        .unwrap_or_else(|| json!([]));
    let details: Vec<ConservationViolation> = serde_json::from_value(violations_value).unwrap();
    assert_eq!(details.len(), 2);
    assert_eq!(details[0].key, "records");
    assert_eq!(details[0].before, json!(5));
    assert_eq!(details[0].after, json!("[missing]"));
}
