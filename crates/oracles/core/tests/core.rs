use serde_json::{json, Value};
use tf_oracles_core::{
    canonical_json, canonicalize, deep_equal, err, ok, pointer_from_segments,
    pretty_canonical_json, segments_from_pointer, with_trace, OracleCtx, OracleResult, PointerSeg,
};

#[test]
fn success_deduplicates_warnings() {
    let result = ok(42u32, [" keep ", "keep", "drop"]);
    match result {
        OracleResult::Success(success) => {
            assert_eq!(success.value, 42);
            assert_eq!(success.warnings, Some(vec!["drop".into(), "keep".into()]));
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
    assert_eq!(failure.trace, Some(vec!["alpha".into(), "beta".into()]));
}

#[test]
fn canonicalizes_nested_values() {
    let ctx = OracleCtx::new("0x1").with_now(0);
    let input = json!({
        "unordered": {"b": 1, "a": [3, 2, Value::Null, -0.0, 1.23456789012345_f64]},
        "timestamp": "2020-01-01T00:00:00Z",
    });

    let canonical = ctx.canonicalize_value(input);
    assert_eq!(
        canonical,
        json!({
            "timestamp": "2020-01-01T00:00:00Z",
            "unordered": {
                "a": [3, 2, null, 0, 1.234567890123],
                "b": 1,
            }
        })
    );
}

#[test]
fn canonical_json_appends_newline() {
    let text = canonical_json(&json!({
        "b": 1,
        "a": [3, 2, null],
    }));
    assert_eq!(text, "{\"a\":[3,2,null],\"b\":1}\n");
}

#[test]
fn pretty_canonical_json_is_indented() {
    let text = pretty_canonical_json(&json!({
        "b": 1,
        "a": [3, 2, null],
    }));
    assert_eq!(text, "{\n  \"a\": [\n    3,\n    2,\n    null\n  ],\n  \"b\": 1\n}\n");
}

#[test]
fn deep_equal_reports_first_difference() {
    let left = json!({ "a": { "b": [1, 2, 3] } });
    let right = json!({ "a": { "b": [1, 2, 4] } });
    let result = deep_equal(&left, &right);
    assert_eq!(result, Err(String::from("/a/b/2")));
}

#[test]
fn deep_equal_reports_object_difference_pointer() {
    let left = json!({ "a": { "b": 1, "c": 2 } });
    let right = json!({ "a": { "b": 1, "c": 3 } });
    let result = deep_equal(&left, &right);
    assert_eq!(result, Err(String::from("/a/c")));
}

#[test]
fn deep_equal_confirms_equality() {
    let left = json!({ "a": { "x": 1, "y": 2 } });
    let right = json!({ "a": { "y": 2, "x": 1 } });
    assert!(deep_equal(&left, &right).is_ok());
}

#[test]
fn pointer_helpers_round_trip() {
    let segments = vec![
        PointerSeg::Key("root".into()),
        PointerSeg::Index(1),
        PointerSeg::Key("~special/segment".into()),
    ];
    let pointer = pointer_from_segments(&segments);
    assert_eq!(pointer, "/root/1/~0special~1segment");
    let parsed = segments_from_pointer(&pointer);
    assert_eq!(parsed, segments);
    assert!(segments_from_pointer("/").is_empty());
}

#[test]
fn canonicalize_sorts_object_keys() {
    let value = json!({ "z": 1, "a": { "m": 2, "n": 1 } });
    let canonical = canonicalize(&value);
    assert_eq!(canonical, json!({ "a": { "m": 2, "n": 1 }, "z": 1 }));
}

#[test]
fn canonicalize_preserves_array_order() {
    let value = json!([3, 1, 2, 1]);
    let canonical = canonicalize(&value);
    assert_eq!(canonical, json!([3, 1, 2, 1]));
}
