use serde_json::Value;
use tflang_l0::proof::{Delta, Effect, NormalizationTarget, Replace, Tag, TransportOp};

#[test]
fn proof_tag_shapes() {
    let d: Delta = Some(Replace { replace: Value::Null });
    let w = Tag::Witness { delta: d, effect: Effect::default() };
    let n = Tag::Normalization { target: NormalizationTarget::Delta };
    let t = Tag::Transport { op: TransportOp::LensProj, region: "r".into() };
    let r = Tag::Refutation { code: "E".into(), msg: Some("oops".into()) };
    let c = Tag::Conservativity { callee: "c".into(), expected: "e".into(), found: "f".into() };
    let tags = vec![w, n, t, r, c];
    assert_eq!(tags.len(), 5);
}
