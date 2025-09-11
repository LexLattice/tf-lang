use tflang_l0::proof::{ProofTag, TransportOp};

#[test]
fn constructs_refutation_tag() {
    let t = ProofTag::Refutation { code: "E".into(), msg: Some("x".into()) };
    match t {
        ProofTag::Refutation { code, .. } => assert_eq!(code, "E"),
        _ => panic!("wrong tag"),
    }
}

#[test]
fn transports_region() {
    let t = ProofTag::Transport { op: TransportOp::LensProj, region: "r0".into() };
    match t {
        ProofTag::Transport { region, .. } => assert_eq!(region, "r0"),
        _ => panic!("wrong tag"),
    }
}
