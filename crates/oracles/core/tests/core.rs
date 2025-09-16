use serde_json::{json, Value};
use tf_oracles_core::{canonical_string, err, ok, with_trace, OracleCtx, OracleResult};

#[test]
fn success_deduplicates_warnings() {
    let result = ok(42u32, [" keep ", "keep", "drop"]);
    match result {
        OracleResult::Success(success) => {
            assert_eq!(success.value, 42);
            assert_eq!(
                success.warnings,
                Some(vec!["drop".to_string(), "keep".to_string()])
            );
        }
        OracleResult::Failure(_) => panic!("expected success"),
    }
}

#[test]
fn error_normalizes_code_and_explain() {
    let failure = err(
        " e_bad_input ",
        "  Something went wrong \n",
        Some(json!({ "field": "x" })),
    );
    assert!(!failure.ok);
    assert_eq!(failure.error.code, "E_BAD_INPUT");
    assert_eq!(failure.error.explain, "Something went wrong");
    assert_eq!(failure.error.details, Some(json!({ "field": "x" })));
}

#[test]
fn trace_is_merged_and_deduped() {
    let base = err("E_FAIL", "bad", None);
    let failure = with_trace(base, ["alpha", "alpha", "beta"]);
    assert_eq!(
        failure.trace,
        Some(vec!["alpha".to_string(), "beta".to_string()])
    );
}

#[test]
fn canonicalizes_nested_objects() {
    let ctx = OracleCtx::new("0x1").with_now(0);
    let input = json!({
        "b": 1,
        "a": [3, 2, Value::Null, -0.0, 1.23456789012345f64],
        "nested": {"y": "x", "x": "y"},
    });

    let canonical = ctx.canonicalize_value(input);
    assert_eq!(
        canonical,
        json!({
            "a": [3, 2, null, 0.0, 1.234567890123],
            "b": 1,
            "nested": {"x": "y", "y": "x"}
        })
    );
}

#[test]
fn canonical_string_matches_expected() {
    let text = canonical_string(&json!({
        "b": 1,
        "a": [3, 2, null],
    }))
    .expect("string");
    assert_eq!(text, "{\"a\":[3,2,null],\"b\":1}");
}

#[test]
fn canonicalizes_key_order_even_when_input_unsorted() {
    let unsorted = json!({ "z": 1, "a": 2, "m": { "y": 3, "x": 4 } });
    let text = canonical_string(&unsorted).expect("string");
    assert_eq!(text, "{\"a\":2,\"m\":{\"x\":4,\"y\":3},\"z\":1}");
}
