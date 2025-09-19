use serde_json::json;

use tf_oracles_core::{diff_canonical, pointer_from_segments, DiffOptions};

#[test]
fn diff_reports_root_pointer() {
    let left = json!(1);
    let right = json!(2);
    let diff = diff_canonical(&left, &right, DiffOptions::default()).expect("diff should exist");
    assert_eq!(diff.pointer, "");
    assert_eq!(diff.left, json!(1));
    assert_eq!(diff.right, json!(2));
}

#[test]
fn diff_uses_missing_sentinel_for_arrays() {
    let left = json!([1, 2, 3]);
    let right = json!([1, 2]);
    let missing = json!("[missing]");
    let diff = diff_canonical(
        &left,
        &right,
        DiffOptions {
            missing_value: Some(&missing),
        },
    )
    .expect("diff should exist");
    assert_eq!(diff.pointer, "/2");
    assert_eq!(diff.left, json!(3));
    assert_eq!(diff.right, json!("[missing]"));
}

#[test]
fn pointer_segments_escape_characters() {
    let pointer = pointer_from_segments(&["a~", "b/"]);
    assert_eq!(pointer, "/a~0/b~1");
}
