use tflang_l0::proof::{ProofTag, DeltaNF, EffectNF, NormalizationTarget, TransportOp};

#[test]
fn constructs_tags() {
    let w = ProofTag::Witness { delta: DeltaNF::None, effect: EffectNF::default() };
    let n = ProofTag::Normalization { target: NormalizationTarget::Delta };
    let t = ProofTag::Transport { op: TransportOp::LensProj, region: "/r".into() };
    let r = ProofTag::Refutation { code: "E_X".into(), msg: None };
    let c = ProofTag::Conservativity { callee: "c".into(), expected: "e".into(), found: "f".into() };
    let kinds = match (&w,&n,&t,&r,&c) {
        (ProofTag::Witness {..}, ProofTag::Normalization {..}, ProofTag::Transport {..}, ProofTag::Refutation {..}, ProofTag::Conservativity {..}) => 5,
        _ => 0
    };
    assert_eq!(kinds,5);
}
