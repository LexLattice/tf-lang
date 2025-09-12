use serde_json::json;
use tflang_l0::model::{Instr, Program};
use tflang_l0::vm::interpreter::VM;
use tflang_l0::vm::opcode::Host;
use tflang_l0::proof::{flush, ProofTag, TransportOp};

struct DummyHost;

impl Host for DummyHost {
    fn lens_project(&self, state: &serde_json::Value, region: &str) -> anyhow::Result<serde_json::Value> {
        Ok(json!({"region": region, "state": state}))
    }
    fn lens_merge(&self, state: &serde_json::Value, _region: &str, substate: &serde_json::Value) -> anyhow::Result<serde_json::Value> {
        Ok(json!({"orig": state, "sub": substate}))
    }
    fn snapshot_make(&self, state: &serde_json::Value) -> anyhow::Result<serde_json::Value> { Ok(state.clone()) }
    fn snapshot_id(&self, _snapshot: &serde_json::Value) -> anyhow::Result<String> { Ok("id".into()) }
    fn diff_apply(&self, state: &serde_json::Value, _delta: &serde_json::Value) -> anyhow::Result<serde_json::Value> { Ok(state.clone()) }
    fn diff_invert(&self, delta: &serde_json::Value) -> anyhow::Result<serde_json::Value> { Ok(delta.clone()) }
    fn journal_record(&self, _plan: &serde_json::Value, _delta: &serde_json::Value, _s0: &str, _s1: &str, _meta: &serde_json::Value) -> anyhow::Result<tflang_l0::model::JournalEntry> {
        Ok(tflang_l0::model::JournalEntry(serde_json::Value::Null))
    }
    fn journal_rewind(&self, world: &tflang_l0::model::World, _entry: &tflang_l0::model::JournalEntry) -> anyhow::Result<tflang_l0::model::World> {
        Ok(tflang_l0::model::World(world.0.clone()))
    }
    fn call_tf(&self, _tf_id: &str, _args: &[serde_json::Value]) -> anyhow::Result<serde_json::Value> { Ok(serde_json::Value::Null) }
}

fn sample_prog() -> Program {
    Program {
        version: "0.1".into(),
        regs: 2,
        instrs: vec![
            Instr::Const { dst: 0, value: json!({}) },
            Instr::LensProj { dst: 1, state: 0, region: "r".into() },
            Instr::Const { dst: 0, value: json!({"x":1}) },
            Instr::Halt,
        ],
    }
}

#[test]
fn dev_proofs_toggles_tags() {
    std::env::set_var("DEV_PROOFS", "1");
    let vm = VM { host: &DummyHost };
    let _ = vm.run(&sample_prog()).unwrap();
    let tags = flush();
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Transport { op: TransportOp::LensProj, .. })));
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Witness { .. })));

    std::env::remove_var("DEV_PROOFS");
    let _ = vm.run(&sample_prog()).unwrap();
    let tags = flush();
    assert!(tags.is_empty());
}
