use serde_json::{json, Value};
use tflang_l0::proof::{Delta, Effect, NormalizationTarget, Replace, ProofTag, TransportOp};

#[test]
fn proof_tag_shapes() {
    let d: Delta = Some(Replace { replace: Value::Null });
    let w = ProofTag::Witness { delta: d, effect: Effect::default() };
    let n = ProofTag::Normalization { target: NormalizationTarget::Delta };
    let t = ProofTag::Transport { op: TransportOp::LensProj, region: "r".into() };
    let r = ProofTag::Refutation { code: "E".into(), msg: Some("oops".into()) };
    let c = ProofTag::Conservativity { callee: "c".into(), expected: "e".into(), found: "f".into() };
    let tags = vec![w, n, t, r, c];
    assert_eq!(tags.len(), 5);
}

#[test]
fn serde_roundtrip_transport() {
    let t = ProofTag::Transport { op: TransportOp::LensProj, region: "r".into() };
    let v = serde_json::to_value(&t).unwrap();
    assert_eq!(v, json!({"kind":"Transport","op":"LENS_PROJ","region":"r"}));
}

#[test]
fn serde_roundtrip_normalization() {
    let n = ProofTag::Normalization { target: NormalizationTarget::Delta };
    let v = serde_json::to_value(&n).unwrap();
    assert_eq!(v, json!({"kind":"Normalization","target":"delta"}));
}
