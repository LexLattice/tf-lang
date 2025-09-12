use serde_json::{json, Value};
use std::fs;
use std::path::Path;
use std::sync::Mutex;
use tflang_l0::model::Program;
use tflang_l0::proof::{flush, reset, ProofTag};
use tflang_l0::vm::interpreter::VM;
use tflang_l0::vm::opcode::Host;

struct DummyHost;

impl Host for DummyHost {
    fn lens_project(&self, state: &Value, region: &str) -> anyhow::Result<Value> {
        Ok(json!({ "region": region, "state": state }))
    }
    fn lens_merge(&self, state: &Value, _region: &str, substate: &Value) -> anyhow::Result<Value> {
        Ok(json!({ "orig": state, "sub": substate }))
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

fn load_vector() -> (Program, Vec<ProofTag>) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/dev/proof_dev.json");
    let data = fs::read_to_string(path).expect("read vector");
    let v: Value = serde_json::from_str(&data).expect("parse vector");
    let prog: Program = serde_json::from_value(v.get("bytecode").cloned().unwrap()).expect("prog");
    let tags: Vec<ProofTag> = serde_json::from_value(v.get("tags").cloned().unwrap()).expect("tags");
    (prog, tags)
}

#[test]
fn dev_proofs_parity_and_toggle() {
    let _g = TEST_LOCK.lock().expect("lock");
    let (prog, expected) = load_vector();
    reset();
    std::env::set_var("DEV_PROOFS", "1");
    let vm = VM { host: &DummyHost };
    vm.run(&prog).expect("vm run");
    let tags = flush();
    assert_eq!(tags, expected);

    reset();
    std::env::remove_var("DEV_PROOFS");
    vm.run(&prog).expect("vm run");
    let tags = flush();
    assert!(tags.is_empty());
}

#[test]
fn dev_proofs_cache_and_reset() {
    let _g = TEST_LOCK.lock().expect("lock");
    let (prog, _) = load_vector();
    reset();
    std::env::set_var("DEV_PROOFS", "1");
    let vm = VM { host: &DummyHost };
    vm.run(&prog).expect("vm run");
    flush();
    std::env::remove_var("DEV_PROOFS");
    vm.run(&prog).expect("vm run");
    assert!(!flush().is_empty());
    reset();
    vm.run(&prog).expect("vm run");
    assert!(flush().is_empty());
}

static TEST_LOCK: Mutex<()> = Mutex::new(());
