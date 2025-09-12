use serde_json::json;
use tflang_l0::proof::{ProofTag, NormalizationTarget};

#[test]
fn proof_tag_normalization_shape() {
    let n = ProofTag::Normalization { target: NormalizationTarget::Delta };
    let v = serde_json::to_value(&n).unwrap();
    assert_eq!(v, json!({"kind":"Normalization","target":"delta"}));
}
