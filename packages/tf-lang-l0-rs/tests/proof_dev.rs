use serde::Deserialize;
use serde_json::{json, Value};
use std::fs;
use std::path::PathBuf;
use tflang_l0::model::{Instr, Program};
use tflang_l0::vm::interpreter::VM;
use tflang_l0::vm::opcode::Host;
use tflang_l0::proof::{flush, emit, enabled, reset, ProofTag, TransportOp};

struct DummyHost;

impl Host for DummyHost {
    fn lens_project(&self, state: &Value, region: &str) -> anyhow::Result<Value> {
        Ok(json!({"region": region, "state": state}))
    }
    fn lens_merge(&self, state: &Value, _region: &str, substate: &Value) -> anyhow::Result<Value> {
        Ok(json!({"orig": state, "sub": substate}))
    }
    fn snapshot_make(&self, state: &Value) -> anyhow::Result<Value> { Ok(state.clone()) }
    fn snapshot_id(&self, _snapshot: &Value) -> anyhow::Result<String> { Ok("id".into()) }
    fn diff_apply(&self, state: &Value, _delta: &Value) -> anyhow::Result<Value> { Ok(state.clone()) }
    fn diff_invert(&self, delta: &Value) -> anyhow::Result<Value> { Ok(delta.clone()) }
    fn journal_record(&self, _plan: &Value, _delta: &Value, _s0: &str, _s1: &str, _meta: &Value) -> anyhow::Result<tflang_l0::model::JournalEntry> {
        Ok(tflang_l0::model::JournalEntry(Value::Null))
    }
    fn journal_rewind(&self, world: &tflang_l0::model::World, _entry: &tflang_l0::model::JournalEntry) -> anyhow::Result<tflang_l0::model::World> {
        Ok(tflang_l0::model::World(world.0.clone()))
    }
    fn call_tf(&self, _tf_id: &str, _args: &[Value]) -> anyhow::Result<Value> { Ok(Value::Null) }
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
    reset();
    let vm = VM { host: &DummyHost };
    let _ = vm.run(&sample_prog()).unwrap();
    let tags = flush();
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Transport { op: TransportOp::LensProj, .. })));
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Witness { .. })));

    std::env::remove_var("DEV_PROOFS");
    reset();
    let _ = vm.run(&sample_prog()).unwrap();
    let tags = flush();
    assert!(tags.is_empty());
}

#[test]
fn caches_env_and_resets() {
    std::env::set_var("DEV_PROOFS", "1");
    reset();
    assert!(enabled());
    std::env::remove_var("DEV_PROOFS");
    assert!(enabled()); // cached
    reset();
    assert!(!enabled());
}

#[test]
fn parallel_logs_isolated() {
    std::env::set_var("DEV_PROOFS", "1");
    reset();
    std::thread::scope(|s| {
        let h1 = s.spawn(|| {
            if enabled() { emit(ProofTag::Refutation { code: "A".into(), msg: None }); }
            flush()
        });
        let h2 = s.spawn(|| {
            if enabled() { emit(ProofTag::Refutation { code: "B".into(), msg: None }); }
            flush()
        });
        let t1 = h1.join().expect("thread1");
        let t2 = h2.join().expect("thread2");
        assert!(t1.iter().all(|t| matches!(t, ProofTag::Refutation { code, .. } if code == "A")));
        assert!(t2.iter().all(|t| matches!(t, ProofTag::Refutation { code, .. } if code == "B")));
    });
    std::env::remove_var("DEV_PROOFS");
    reset();
}

#[derive(Deserialize)]
struct ProofVector {
    bytecode: Program,
    expected_tags: Vec<ProofTag>,
}

fn load_vector() -> ProofVector {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/proof_tags.json");
    let data = fs::read_to_string(path).unwrap();
    serde_json::from_str(&data).unwrap()
}

#[test]
fn vector_parity() {
    let vec = load_vector();
    std::env::set_var("DEV_PROOFS", "1");
    reset();
    let vm = VM { host: &DummyHost };
    let _ = vm.run(&vec.bytecode).unwrap();
    let tags = flush();
    assert_eq!(tags, vec.expected_tags);

    std::env::remove_var("DEV_PROOFS");
    reset();
    let _ = vm.run(&vec.bytecode).unwrap();
    let tags = flush();
    assert!(tags.is_empty());
}
