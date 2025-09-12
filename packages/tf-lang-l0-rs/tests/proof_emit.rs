use serde_json::{json, Value};
use tflang_l0::model::bytecode::{Instr, Program};
use tflang_l0::model::{JournalEntry, World};
use tflang_l0::proof::{self, ProofTag};
use tflang_l0::vm::{opcode::Host, VM};

struct DummyHost;

impl Host for DummyHost {
    fn lens_project(&self, state: &Value, region: &str) -> anyhow::Result<Value> {
        Ok(json!({ "region": region, "state": state.clone() }))
    }
    fn lens_merge(&self, state: &Value, _region: &str, sub: &Value) -> anyhow::Result<Value> {
        Ok(json!({ "orig": state.clone(), "sub": sub.clone() }))
    }
    fn snapshot_make(&self, state: &Value) -> anyhow::Result<Value> { Ok(state.clone()) }
    fn snapshot_id(&self, snapshot: &Value) -> anyhow::Result<String> {
        Ok(format!("id:{snapshot}"))
    }
    fn diff_apply(&self, state: &Value, _delta: &Value) -> anyhow::Result<Value> { Ok(state.clone()) }
    fn diff_invert(&self, delta: &Value) -> anyhow::Result<Value> {
        Ok(json!({"invert": delta.clone()}))
    }
    fn journal_record(
        &self,
        _plan: &Value,
        delta: &Value,
        s0: &str,
        s1: &str,
        _meta: &Value,
    ) -> anyhow::Result<JournalEntry> {
        Ok(JournalEntry(json!({"delta": delta.clone(), "from": s0, "to": s1})))
    }
    fn journal_rewind(&self, world: &World, _entry: &JournalEntry) -> anyhow::Result<World> {
        Ok(World(world.0.clone()))
    }
    fn call_tf(&self, _id: &str, _args: &[Value]) -> anyhow::Result<Value> {
        Ok(Value::Null)
    }
}

#[test]
fn tags_emitted_with_env() {
    std::env::set_var("DEV_PROOFS", "1");
    let prog = Program {
        version: "0.1".into(),
        regs: 3,
        instrs: vec![
            Instr::Const { dst: 0, value: json!({"a":1}) },
            Instr::LensProj { dst: 1, state: 0, region: "r".into() },
            Instr::Call { dst: 2, tf_id: "tf://missing@0.1".into(), args: vec![] },
            Instr::Halt,
        ],
    };
    let vm = VM { host: &DummyHost };
    vm.run(&prog).unwrap();
    let tags = proof::take();
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Witness { .. })));
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Normalization { .. })));
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Transport { .. })));
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Conservativity { .. })));
}

#[test]
fn no_tags_without_env() {
    std::env::remove_var("DEV_PROOFS");
    let prog = Program {
        version: "0.1".into(),
        regs: 3,
        instrs: vec![
            Instr::Const { dst: 0, value: json!({"a":1}) },
            Instr::LensProj { dst: 1, state: 0, region: "r".into() },
            Instr::Call { dst: 2, tf_id: "tf://missing@0.1".into(), args: vec![] },
            Instr::Halt,
        ],
    };
    let vm = VM { host: &DummyHost };
    vm.run(&prog).unwrap();
    let tags = proof::take();
    assert!(tags.is_empty());
}

#[test]
fn refutation_on_assert() {
    std::env::set_var("DEV_PROOFS", "1");
    let prog = Program {
        version: "0.1".into(),
        regs: 1,
        instrs: vec![
            Instr::Const { dst: 0, value: json!(false) },
            Instr::Assert { pred: 0, msg: "nope".into() },
        ],
    };
    let vm = VM { host: &DummyHost };
    assert!(vm.run(&prog).is_err());
    let tags = proof::take();
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Refutation { .. })));
}
