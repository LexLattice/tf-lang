use anyhow::Result;
use serde_json::json;
use tflang_l0::canon::{blake3_hex, canonical_json_bytes};
use tflang_l0::model::{Instr, Program};
use tflang_l0::model::{JournalEntry, World};
use tflang_l0::vm::interpreter::VM;
use tflang_l0::vm::opcode::Host;

struct DummyHost;

impl Host for DummyHost {
    fn lens_project(
        &self,
        state: &serde_json::Value,
        region: &str,
    ) -> anyhow::Result<serde_json::Value> {
        Ok(json!({ "region": region, "state": state }))
    }
    fn lens_merge(
        &self,
        state: &serde_json::Value,
        _region: &str,
        substate: &serde_json::Value,
    ) -> anyhow::Result<serde_json::Value> {
        let mut obj = serde_json::Map::new();
        obj.insert("orig".into(), state.clone());
        obj.insert("sub".into(), substate.clone());
        Ok(serde_json::Value::Object(obj))
    }
    fn snapshot_make(&self, state: &serde_json::Value) -> anyhow::Result<serde_json::Value> {
        Ok(state.clone())
    }
    fn snapshot_id(&self, snapshot: &serde_json::Value) -> anyhow::Result<String> {
        let bytes = canonical_json_bytes(snapshot)?;
        Ok(format!("id:{}", blake3_hex(&bytes)))
    }
    fn diff_apply(
        &self,
        state: &serde_json::Value,
        delta: &serde_json::Value,
    ) -> anyhow::Result<serde_json::Value> {
        // Support delta = { "append": v } on array states; else return delta passthrough
        if let Some(arr) = state.as_array() {
            if let Some(v) = delta.get("append") {
                let mut new = arr.clone();
                new.push(v.clone());
                return Ok(serde_json::Value::Array(new));
            }
        }
        Ok(delta.clone())
    }
    fn diff_invert(&self, delta: &serde_json::Value) -> anyhow::Result<serde_json::Value> {
        Ok(json!({ "invert": delta }))
    }
    fn journal_record(
        &self,
        _plan: &serde_json::Value,
        delta: &serde_json::Value,
        s0: &str,
        s1: &str,
        _meta: &serde_json::Value,
    ) -> anyhow::Result<JournalEntry> {
        Ok(JournalEntry(
            json!({ "delta": delta, "from": s0, "to": s1 }),
        ))
    }
    fn journal_rewind(&self, world: &World, entry: &JournalEntry) -> anyhow::Result<World> {
        // Inverse of {append:v} is "pop last element" from array world
        let mut wv = world.0.clone();
        if let Some(arr) = wv.as_array_mut() {
            if entry.0.get("delta").and_then(|d| d.get("append")).is_some() && !arr.is_empty() {
                arr.pop();
            }
        }
        Ok(World(wv))
    }
    fn call_tf(
        &self,
        tf_id: &str,
        args: &[serde_json::Value],
    ) -> anyhow::Result<serde_json::Value> {
        match tf_id {
            "tf://plan/delta@0.1" => {
                // args: [state, plan_value]; return {"append": plan_value}
                let plan_val = args.get(1).cloned().unwrap_or(json!(null));
                Ok(json!({ "append": plan_val }))
            }
            "tf://plan/simulate@0.1" => Ok(json!({
                "delta": args.get(1).cloned().unwrap_or(json!(null)),
                "world": args.get(0).cloned().unwrap_or(json!(null))
            })),
            "tf://eq/json@0.1" => {
                let a = args.get(0).cloned().unwrap_or(json!(null));
                let b = args.get(1).cloned().unwrap_or(json!(null));
                let ca = canonical_json_bytes(&a)?;
                let cb = canonical_json_bytes(&b)?;
                Ok(json!(ca == cb))
            }
            _ => Ok(json!(null)),
        }
    }
}

#[test]
fn vm_runs_halt_program() -> Result<()> {
    let prog = Program {
        version: "0.1".into(),
        regs: 2,
        instrs: vec![Instr::Halt],
    };
    let mut vm = VM::new(&DummyHost);
    let out = vm.run(&prog)?;
    assert_eq!(out, serde_json::Value::Null);
    Ok(())
}

#[test]
fn vm_basic_ops() -> Result<()> {
    let prog = Program {
        version: "0.1".into(),
        regs: 6,
        instrs: vec![
            Instr::Const {
                dst: 0,
                value: json!({"state": 1}),
            },
            Instr::LensProj {
                dst: 1,
                state: 0,
                region: "legal.clauses".into(),
            },
            Instr::LensMerge {
                dst: 2,
                state: 0,
                region: "legal.clauses".into(),
                sub: 1,
            },
            Instr::SnapMake { dst: 3, state: 2 },
            Instr::SnapId {
                dst: 4,
                snapshot: 3,
            },
            Instr::Halt,
        ],
    };
    let mut vm = VM::new(&DummyHost);
    let out = vm.run(&prog)?;
    // r0 is returned by our VM.run. It should be untouched Null unless overwritten.
    assert_eq!(out, serde_json::Value::Null);
    Ok(())
}

#[test]
fn law_rewind_apply_id_pair_ids_equal() -> Result<()> {
    // Program returns r0 = Pair[id_before, id_after_rewind] so test can compare equality.
    let prog = Program {
        version: "0.1".into(),
        regs: 13,
        instrs: vec![
            // r0 = initial state (array)
            Instr::Const {
                dst: 0,
                value: json!([1, 2]),
            },
            // r12 = plan value (append 3)
            Instr::Const {
                dst: 12,
                value: json!(3),
            },
            // r1 = snap0, r2 = id0
            Instr::SnapMake { dst: 1, state: 0 },
            Instr::SnapId {
                dst: 2,
                snapshot: 1,
            },
            // r3 = delta via CALL (state, plan) -> {"append": plan}
            Instr::Call {
                dst: 3,
                tf_id: "tf://plan/delta@0.1".into(),
                args: vec![0, 12],
            },
            // r4 = state1 after apply
            Instr::DiffApply {
                dst: 4,
                state: 0,
                delta: 3,
            },
            // r5 = snap1, r6 = id1
            Instr::SnapMake { dst: 5, state: 4 },
            Instr::SnapId {
                dst: 6,
                snapshot: 5,
            },
            // r7 = meta {}
            Instr::Const {
                dst: 7,
                value: json!({}),
            },
            // r8 = journal entry
            Instr::JournalRec {
                dst: 8,
                plan: 12,
                delta: 3,
                snap0: 2,
                snap1: 6,
                meta: 7,
            },
            // r9 = world_prev = rewind(world_after, entry)
            Instr::JournalRew {
                dst: 9,
                world: 4,
                entry: 8,
            },
            // r10 = snap_prev, r11 = id_prev
            Instr::SnapMake { dst: 10, state: 9 },
            Instr::SnapId {
                dst: 11,
                snapshot: 10,
            },
            // r0 = Pack(Pair, id_before, id_prev)
            // r12 = eq(id_before, id_prev)
            Instr::Call {
                dst: 12,
                tf_id: "tf://eq/json@0.1".into(),
                args: vec![2, 11],
            },
            // assert equality
            Instr::Assert {
                pred: 12,
                msg: "rewind law violated".into(),
            },
            Instr::Pack {
                dst: 0,
                tag: "Pair".into(),
                regs: vec![2, 11],
            },
            Instr::Halt,
        ],
    };
    let mut vm = VM::new(&DummyHost);
    let out = vm.run(&prog)?;
    let obj = out
        .get("replace")
        .and_then(|v| v.as_object())
        .expect("Pair object");
    assert_eq!(obj.get("tag").and_then(|t| t.as_str()), Some("Pair"));
    let vals = obj
        .get("values")
        .and_then(|v| v.as_array())
        .expect("values");
    assert_eq!(
        vals[0], vals[1],
        "snapshot ids should be equal after rewind"
    );
    Ok(())
}
