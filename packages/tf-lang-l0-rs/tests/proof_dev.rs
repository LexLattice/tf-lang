use serde_json::json;
use serial_test::serial;
use std::fs;
use tflang_l0::model::{Instr, Program};
use tflang_l0::proof::{flush, ProofTag, TransportOp, reset_dev_proofs_for_test};
use tflang_l0::vm::interpreter::VM;
use tflang_l0::vm::opcode::Host;

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
        regs: 3,
        instrs: vec![
            Instr::Const { dst: 0, value: json!({"x":0}) },
            Instr::LensProj { dst: 1, state: 0, region: "/x".into() },
            Instr::Const { dst: 2, value: json!(1) },
            Instr::LensMerge { dst: 0, state: 0, region: "/x".into(), sub: 2 },
            Instr::Halt,
        ],
    }
}

#[test]
#[serial]
fn dev_proofs_toggle() {
    std::env::set_var("DEV_PROOFS", "1");
    reset_dev_proofs_for_test();
    let vm = VM { host: &DummyHost };
    let _ = vm.run(&sample_prog()).unwrap();
    let tags = flush();
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Transport { op: TransportOp::LensProj, .. })));
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Witness { .. })));
    std::env::remove_var("DEV_PROOFS");
    reset_dev_proofs_for_test();
    let _ = vm.run(&sample_prog()).unwrap();
    let tags = flush();
    assert!(tags.is_empty());
}

#[test]
#[serial]
fn cache_and_reset() {
    let vm = VM { host: &DummyHost };
    std::env::set_var("DEV_PROOFS", "1");
    reset_dev_proofs_for_test();
    let _ = vm.run(&sample_prog()).unwrap();
    assert!(!flush().is_empty());
    std::env::set_var("DEV_PROOFS", "0");
    let _ = vm.run(&sample_prog()).unwrap();
    assert!(!flush().is_empty()); // still cached
    reset_dev_proofs_for_test();
    let _ = vm.run(&sample_prog()).unwrap();
    assert!(flush().is_empty());
    std::env::remove_var("DEV_PROOFS");
}

#[test]
#[serial]
fn parallel_logs_isolated() {
    std::env::set_var("DEV_PROOFS", "1");
    reset_dev_proofs_for_test();
    let first = std::thread::spawn(|| {
        let vm = VM { host: &DummyHost };
        let _ = vm.run(&sample_prog()).unwrap();
        flush()
    }).join().unwrap();
    let second = std::thread::spawn(|| {
        let vm = VM { host: &DummyHost };
        let _ = vm.run(&sample_prog()).unwrap();
        flush()
    }).join().unwrap();
    assert!(!first.is_empty());
    assert!(!second.is_empty());
    std::env::remove_var("DEV_PROOFS");
}

#[test]
#[serial]
fn shared_vector_parity() {
    let data = fs::read_to_string("../../tests/proof-tags.json").unwrap();
    let v: serde_json::Value = serde_json::from_str(&data).unwrap();
    let prog: Program = serde_json::from_value(v.get("program").cloned().unwrap()).unwrap();
    let expected: Vec<ProofTag> = serde_json::from_value(v.get("expectedTags").cloned().unwrap()).unwrap();

    std::env::set_var("DEV_PROOFS", "1");
    reset_dev_proofs_for_test();
    let vm = VM { host: &DummyHost };
    let _ = vm.run(&prog).unwrap();
    let tags = flush();
    assert_eq!(tags, expected);

    std::env::remove_var("DEV_PROOFS");
    reset_dev_proofs_for_test();
    let _ = vm.run(&prog).unwrap();
    let tags = flush();
    assert!(tags.is_empty());
}
