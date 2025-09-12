use serde_json::{json, Value};
use tflang_l0::proof::{Delta, Effect, NormalizationTarget, ProofTag, Replace, TransportOp};
use tflang_l0::vm::interpreter::VM;
use tflang_l0::vm::opcode::Host;
use tflang_l0::model::{Instr, Program};
use anyhow::Result;

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

struct MiniHost;

impl Host for MiniHost {
    fn lens_project(&self, state: &Value, region: &str) -> anyhow::Result<Value> {
        Ok(json!({"region": region, "state": state}))
    }
    fn lens_merge(&self, state: &Value, _region: &str, substate: &Value) -> anyhow::Result<Value> {
        Ok(json!({"orig": state, "sub": substate}))
    }
    fn snapshot_make(&self, state: &Value) -> anyhow::Result<Value> { Ok(state.clone()) }
    fn snapshot_id(&self, _snapshot: &Value) -> anyhow::Result<String> { Ok("id".into()) }
    fn diff_apply(&self, state: &Value, delta: &Value) -> anyhow::Result<Value> {
        if let Some(arr) = state.as_array() {
            if let Some(v) = delta.get("append") {
                let mut new = arr.clone();
                new.push(v.clone());
                return Ok(Value::Array(new));
            }
        }
        Ok(state.clone())
    }
    fn diff_invert(&self, delta: &Value) -> anyhow::Result<Value> { Ok(json!({"invert": delta})) }
    fn journal_record(&self, _plan: &Value, delta: &Value, s0: &str, s1: &str, _meta: &Value) -> anyhow::Result<tflang_l0::model::JournalEntry> {
        Ok(tflang_l0::model::JournalEntry(json!({"delta": delta, "from": s0, "to": s1})))
    }
    fn journal_rewind(&self, world: &tflang_l0::model::World, _entry: &tflang_l0::model::JournalEntry) -> anyhow::Result<tflang_l0::model::World> {
        Ok(world.clone())
    }
    fn call_tf(&self, tf_id: &str, _args: &[Value]) -> anyhow::Result<Value> {
        if tf_id == "tf://missing@0.1" {
            Ok(Value::Null)
        } else {
            Ok(Value::Null)
        }
    }
}

#[test]
fn emits_tags_when_enabled() -> Result<()> {
    std::env::set_var("DEV_PROOFS", "1");
    let prog = Program {
        version: "0.1".into(),
        regs: 3,
        instrs: vec![
            Instr::Const { dst: 0, value: json!([]) },
            Instr::Const { dst: 1, value: json!({"append": 1}) },
            Instr::DiffApply { dst: 0, state: 0, delta: 1 },
            Instr::LensProj { dst: 2, state: 0, region: "r".into() },
            Instr::Halt,
        ],
    };
    let mut vm = VM::new(&MiniHost);
    vm.run(&prog)?;
    let tags = vm.tags.unwrap();
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Witness { .. })));
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Transport { .. })));
    assert!(tags.iter().filter(|t| matches!(t, ProofTag::Normalization { .. })).count() > 0);
    std::env::remove_var("DEV_PROOFS");
    Ok(())
}

#[test]
fn refutation_and_conservativity() -> Result<()> {
    std::env::set_var("DEV_PROOFS", "1");
    let prog = Program {
        version: "0.1".into(),
        regs: 2,
        instrs: vec![
            Instr::Const { dst: 0, value: json!(0) },
            Instr::Assert { pred: 0, msg: "no".into() },
        ],
    };
    let mut vm = VM::new(&MiniHost);
    assert!(vm.run(&prog).is_err());
    let tags = vm.tags.unwrap();
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Refutation { .. })));

    let prog2 = Program {
        version: "0.1".into(),
        regs: 1,
        instrs: vec![Instr::Call { dst: 0, tf_id: "tf://missing@0.1".into(), args: vec![] }],
    };
    let mut vm2 = VM::new(&MiniHost);
    vm2.run(&prog2)?;
    let tags2 = vm2.tags.unwrap();
    assert!(tags2.iter().any(|t| matches!(t, ProofTag::Conservativity { .. })));
    std::env::remove_var("DEV_PROOFS");
    Ok(())
}

#[test]
fn silent_when_disabled() -> Result<()> {
    std::env::remove_var("DEV_PROOFS");
    let prog = Program { version: "0.1".into(), regs: 1, instrs: vec![Instr::Halt] };
    let mut vm = VM::new(&MiniHost);
    vm.run(&prog)?;
    assert!(vm.tags.is_none());
    Ok(())
}
