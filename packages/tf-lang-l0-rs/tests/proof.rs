use serde_json::{json, Value};
use tflang_l0::proof::{self, Delta, Effect, NormalizationTarget, Replace, ProofTag, TransportOp};
use tflang_l0::vm::interpreter::VM;
use tflang_l0::vm::opcode::Host;
use tflang_l0::model::bytecode::{Program, Instr};
use tflang_l0::model::{World, JournalEntry};
use once_cell::sync::Lazy;
use std::sync::Mutex;

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

struct StubHost;

impl Host for StubHost {
    fn lens_project(&self, state: &Value, _region: &str) -> anyhow::Result<Value> { Ok(state.clone()) }
    fn lens_merge(&self, state: &Value, _region: &str, _sub: &Value) -> anyhow::Result<Value> { Ok(state.clone()) }
    fn snapshot_make(&self, state: &Value) -> anyhow::Result<Value> { Ok(state.clone()) }
    fn snapshot_id(&self, _snapshot: &Value) -> anyhow::Result<String> { Ok(String::new()) }
    fn diff_apply(&self, state: &Value, _delta: &Value) -> anyhow::Result<Value> { Ok(state.clone()) }
    fn diff_invert(&self, delta: &Value) -> anyhow::Result<Value> { Ok(delta.clone()) }
    fn journal_record(&self, _plan: &Value, _delta: &Value, _s0: &str, _s1: &str, _meta: &Value) -> anyhow::Result<JournalEntry> { Ok(JournalEntry(Value::Null)) }
    fn journal_rewind(&self, _world: &World, _entry: &JournalEntry) -> anyhow::Result<World> { Ok(World(Value::Null)) }
    fn call_tf(&self, _tf_id: &str, _args: &[Value]) -> anyhow::Result<Value> { Ok(Value::Null) }
}

struct FailHost;

impl Host for FailHost {
    fn lens_project(&self, state: &Value, _region: &str) -> anyhow::Result<Value> { Ok(state.clone()) }
    fn lens_merge(&self, state: &Value, _region: &str, _sub: &Value) -> anyhow::Result<Value> { Ok(state.clone()) }
    fn snapshot_make(&self, state: &Value) -> anyhow::Result<Value> { Ok(state.clone()) }
    fn snapshot_id(&self, _snapshot: &Value) -> anyhow::Result<String> { Ok(String::new()) }
    fn diff_apply(&self, state: &Value, _delta: &Value) -> anyhow::Result<Value> { Ok(state.clone()) }
    fn diff_invert(&self, delta: &Value) -> anyhow::Result<Value> { Ok(delta.clone()) }
    fn journal_record(&self, _plan: &Value, _delta: &Value, _s0: &str, _s1: &str, _meta: &Value) -> anyhow::Result<JournalEntry> { Ok(JournalEntry(Value::Null)) }
    fn journal_rewind(&self, _world: &World, _entry: &JournalEntry) -> anyhow::Result<World> { Ok(World(Value::Null)) }
    fn call_tf(&self, tf_id: &str, _args: &[Value]) -> anyhow::Result<Value> { anyhow::bail!("fail {tf_id}") }
}

static TEST_MUTEX: Lazy<Mutex<()>> = Lazy::new(|| Mutex::new(()));

#[test]
fn emits_tags_with_flag() {
    let _g = TEST_MUTEX.lock().unwrap();
    std::env::set_var("DEV_PROOFS", "1");
    let host = StubHost;
    let vm = VM { host: &host };
    let prog = Program { version: "0.1".into(), regs: 2, instrs: vec![
        Instr::Const { dst: 0, value: json!({}) },
        Instr::LensProj { dst: 1, state: 0, region: "/r".into() },
    ]};
    vm.run(&prog).unwrap();
    let tags = proof::take();
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Transport { .. })));
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Witness { .. })));
    std::env::remove_var("DEV_PROOFS");
}

#[test]
fn no_tags_without_flag() {
    let _g = TEST_MUTEX.lock().unwrap();
    std::env::remove_var("DEV_PROOFS");
    let host = StubHost;
    let vm = VM { host: &host };
    let prog = Program { version: "0.1".into(), regs: 1, instrs: vec![
        Instr::Const { dst: 0, value: Value::Null },
    ]};
    vm.run(&prog).unwrap();
    assert!(proof::take().is_empty());
}

#[test]
fn refutation_and_conservativity() {
    let _g = TEST_MUTEX.lock().unwrap();
    std::env::set_var("DEV_PROOFS", "1");
    let host = StubHost;
    let vm = VM { host: &host };
    let prog = Program { version: "0.1".into(), regs: 1, instrs: vec![
        Instr::Const { dst: 0, value: json!(false) },
        Instr::Assert { pred: 0, msg: "oops".into() },
    ]};
    assert!(vm.run(&prog).is_err());
    let tags = proof::take();
    assert!(tags.iter().any(|t| matches!(t, ProofTag::Refutation { code, .. } if code == "ASSERT")));

    let fail = FailHost;
    let vm2 = VM { host: &fail };
    let prog2 = Program { version: "0.1".into(), regs: 1, instrs: vec![
        Instr::Call { dst: 0, tf_id: "x".into(), args: vec![] },
    ]};
    assert!(vm2.run(&prog2).is_err());
    let tags2 = proof::take();
    assert!(tags2.iter().any(|t| matches!(t, ProofTag::Conservativity { callee, .. } if callee == "x")));
    std::env::remove_var("DEV_PROOFS");
}
