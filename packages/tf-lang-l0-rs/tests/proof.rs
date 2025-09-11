use tflang_l0::proof::{ProofTag, NormalizationTarget, TransportOp};
use tflang_l0::model::Effects;

#[test]
fn constructs_tags() {
    let w = ProofTag::Witness { delta: serde_json::Value::Null, effect: Effects::default() };
    let n = ProofTag::Normalization { target: NormalizationTarget::Delta };
    let t = ProofTag::Transport { op: TransportOp::LensProj, region: "r1".to_string() };
    let r = ProofTag::Refutation { code: "X".to_string(), msg: Some("oops".to_string()) };
    let c = ProofTag::Conservativity {
        callee: "f".to_string(),
        expected: "a".to_string(),
        found: "b".to_string(),
    };
    let tags = vec![w, n, t, r, c];
    assert_eq!(tags.len(), 5);
}
