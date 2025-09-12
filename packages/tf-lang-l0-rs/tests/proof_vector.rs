use std::fs;
use std::path::PathBuf;
use serde::Deserialize;
use serde_json::json;
use tflang_l0::model::Program;
use tflang_l0::vm::interpreter::VM;
use tflang_l0::vm::opcode::Host;
use tflang_l0::proof::{flush, reset_for_test, ProofTag};

#[derive(Deserialize)]
struct Vector {
    bytecode: Program,
    expected_tags: Vec<ProofTag>,
}

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

fn load_vector() -> Vector {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/proof_tags.json");
    let data = fs::read_to_string(path).unwrap();
    serde_json::from_str(&data).unwrap()
}

#[test]
fn rust_matches_expected_tags() {
    std::env::set_var("DEV_PROOFS", "1");
    let vec = load_vector();
    let vm = VM { host: &DummyHost };
    let _ = vm.run(&vec.bytecode).unwrap();
    assert_eq!(flush(), vec.expected_tags);

    std::env::remove_var("DEV_PROOFS");
    reset_for_test();
    let _ = vm.run(&vec.bytecode).unwrap();
    assert!(flush().is_empty());
}
