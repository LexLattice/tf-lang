use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use tflang_l0::canon::{blake3_hex, canonical_json_bytes};
use tflang_l0::model::{Instr, Program};
use tflang_l0::vm::interpreter::VM;
use tflang_l0::vm::opcode::Host;

// Basic host used in unit tests
struct DummyHost;

impl Host for DummyHost {
    fn lens_project(&self, state: &Value, region: &str) -> Result<Value> {
        Ok(ptr_get(state, region))
    }
    fn lens_merge(&self, state: &Value, region: &str, sub: &Value) -> Result<Value> {
        Ok(ptr_set(state, region, sub))
    }
    fn snapshot_make(&self, state: &Value) -> Result<Value> {
        Ok(state.clone())
    }
    fn snapshot_id(&self, snapshot: &Value) -> Result<String> {
        let bytes = canonical_json_bytes(snapshot)?;
        Ok(format!("id:{}", blake3_hex(&bytes)))
    }
    fn diff_apply(&self, state: &Value, delta: &Value) -> Result<Value> {
        if delta.is_null() {
            return Ok(state.clone());
        }
        if let Some(replace_val) = delta.get("replace") {
            return Ok(replace_val.clone());
        }
        bail!("E_DELTA_FORM")
    }
    fn diff_invert(&self, delta: &Value) -> Result<Value> {
        Ok(json!({ "invert": delta }))
    }
    fn journal_record(
        &self,
        _plan: &Value,
        delta: &Value,
        s0: &str,
        s1: &str,
        _meta: &Value,
    ) -> Result<tflang_l0::model::JournalEntry> {
        Ok(tflang_l0::model::JournalEntry(json!({
            "delta": delta,
            "from": s0,
            "to": s1
        })))
    }
    fn journal_rewind(
        &self,
        world: &tflang_l0::model::World,
        _entry: &tflang_l0::model::JournalEntry,
    ) -> Result<tflang_l0::model::World> {
        Ok(world.clone())
    }
    fn call_tf(&self, tf_id: &str, args: &[Value]) -> Result<Value> {
        match tf_id {
            "tf://eq/json@0.1" => {
                let a = args.get(0).cloned().unwrap_or(Value::Null);
                let b = args.get(1).cloned().unwrap_or(Value::Null);
                let ca = canonical_json_bytes(&a)?;
                let cb = canonical_json_bytes(&b)?;
                Ok(Value::Bool(ca == cb))
            }
            "tf://plan/delta@0.1" => {
                let lhs = args.get(0).cloned().unwrap_or(Value::Null);
                let rhs = args.get(1).cloned().unwrap_or(Value::Null);
                let lbytes = canonical_json_bytes(&lhs)?;
                let rbytes = canonical_json_bytes(&rhs)?;
                if lbytes == rbytes {
                    Ok(Value::Null)
                } else {
                    Ok(json!({ "replace": rhs }))
                }
            }
            _ => tflang_l0::ops::call(tf_id, args),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct Effect {
    read: Vec<String>,
    write: Vec<String>,
    external: Vec<String>,
}

struct EffectHost<H: Host> {
    inner: H,
    reads: RefCell<BTreeSet<String>>,
    writes: RefCell<BTreeSet<String>>,
    externals: RefCell<BTreeSet<String>>,
    journal: RefCell<Vec<Value>>,
}

impl<H: Host> EffectHost<H> {
    fn new(inner: H) -> Self {
        Self {
            inner,
            reads: RefCell::new(BTreeSet::new()),
            writes: RefCell::new(BTreeSet::new()),
            externals: RefCell::new(BTreeSet::new()),
            journal: RefCell::new(Vec::new()),
        }
    }
    fn normalize(&self) -> Effect {
        let mut read: Vec<String> = self.reads.borrow().iter().cloned().collect();
        if read.len() > 1 && read.contains(&"/".to_string()) {
            read.retain(|p| p != "/");
        }
        let mut write: Vec<String> = self.writes.borrow().iter().cloned().collect();
        if write.len() > 1 && write.contains(&"/".to_string()) {
            write.retain(|p| p != "/");
        }
        let external: Vec<String> = self.externals.borrow().iter().cloned().collect();
        Effect {
            read,
            write,
            external,
        }
    }
}

impl<H: Host> Host for EffectHost<H> {
    fn lens_project(&self, state: &Value, region: &str) -> Result<Value> {
        self.reads.borrow_mut().insert(region.to_string());
        Ok(ptr_get(state, region))
    }
    fn lens_merge(&self, state: &Value, region: &str, sub: &Value) -> Result<Value> {
        self.reads.borrow_mut().insert(region.to_string());
        self.writes.borrow_mut().insert(region.to_string());
        Ok(ptr_set(state, region, sub))
    }
    fn snapshot_make(&self, state: &Value) -> Result<Value> {
        self.reads.borrow_mut().insert("/".into());
        self.inner.snapshot_make(state)
    }
    fn snapshot_id(&self, snapshot: &Value) -> Result<String> {
        self.inner.snapshot_id(snapshot)
    }
    fn diff_apply(&self, state: &Value, delta: &Value) -> Result<Value> {
        self.inner.diff_apply(state, delta)
    }
    fn diff_invert(&self, delta: &Value) -> Result<Value> {
        self.inner.diff_invert(delta)
    }
    fn journal_record(
        &self,
        plan: &Value,
        delta: &Value,
        s0: &str,
        s1: &str,
        meta: &Value,
    ) -> Result<tflang_l0::model::JournalEntry> {
        let entry = self.inner.journal_record(plan, delta, s0, s1, meta)?;
        self.journal.borrow_mut().push(delta.clone());
        Ok(entry)
    }
    fn journal_rewind(
        &self,
        world: &tflang_l0::model::World,
        entry: &tflang_l0::model::JournalEntry,
    ) -> Result<tflang_l0::model::World> {
        self.inner.journal_rewind(world, entry)
    }
    fn call_tf(&self, tf_id: &str, args: &[Value]) -> Result<Value> {
        self.externals.borrow_mut().insert(tf_id.to_string());
        self.inner.call_tf(tf_id, args)
    }
}

#[derive(Deserialize)]
struct Vector {
    name: String,
    bytecode: Program,
    inputs: Option<BTreeMap<String, Value>>,
    expected: Expected,
}

#[derive(Deserialize)]
struct Expected {
    delta: Option<Value>,
    effect: Effect,
    error: Option<String>,
    journal: Option<Vec<Value>>,
}

#[derive(Serialize)]
struct ReportEntry {
    name: String,
    delta: Value,
    effect: Effect,
    delta_hash: String,
    effect_hash: String,
    journal: Vec<Value>,
    journal_hash: String,
}

fn unescape(s: &str) -> String {
    s.replace("~1", "/").replace("~0", "~")
}

fn ptr_get(value: &Value, ptr: &str) -> Value {
    if ptr == "/" {
        return value.clone();
    }
    let parts: Vec<String> = ptr.split('/').skip(1).map(unescape).collect();
    let mut cur = value;
    for p in parts {
        match cur {
            Value::Object(map) => {
                if let Some(next) = map.get(&p) {
                    cur = next;
                } else {
                    return Value::Null;
                }
            }
            Value::Array(arr) => {
                match p.parse::<usize>() {
                    Ok(idx) => {
                        if let Some(next) = arr.get(idx) {
                            cur = next;
                        } else {
                            return Value::Null;
                        }
                    }
                    Err(_) => return Value::Null,
                }
            }
            _ => return Value::Null,
        }
    }
    cur.clone()
}

fn ptr_set(value: &Value, ptr: &str, sub: &Value) -> Value {
    if ptr == "/" {
        return sub.clone();
    }
    let parts: Vec<String> = ptr.split('/').skip(1).map(unescape).collect();
    let mut out = value.clone();
    let mut cur = &mut out;
    for p in &parts[..parts.len() - 1] {
        match cur {
            Value::Object(map) => {
                cur = map
                    .entry(p.clone())
                    .or_insert(Value::Object(serde_json::Map::new()));
            }
            Value::Array(arr) => {
                let idx: usize = match p.parse() {
                    Ok(i) => i,
                    Err(_) => return Value::Null,
                };
                if idx >= arr.len() {
                    arr.resize(idx + 1, Value::Object(serde_json::Map::new()));
                }
                cur = &mut arr[idx];
            }
            _ => return Value::Null,
        }
    }
    let last = parts.last().unwrap();
    match cur {
        Value::Object(map) => {
            map.insert(last.clone(), sub.clone());
        }
        Value::Array(arr) => {
            let idx: usize = match last.parse() {
                Ok(i) => i,
                Err(_) => return Value::Null,
            };
            if idx >= arr.len() {
                arr.resize(idx + 1, Value::Object(serde_json::Map::new()));
            }
            arr[idx] = sub.clone();
        }
        _ => return Value::Null,
    }
    out
}

fn lint_vector(v: &Vector) -> Result<()> {
    if v.bytecode.version != "L0" {
        bail!("unsupported bytecode version: {}", v.bytecode.version);
    }
    let ptr = |p: &str| {
        if !p.starts_with('/') {
            bail!("pointer must start with '/': {}", p);
        }
        Ok::<_, anyhow::Error>(())
    };
    for ins in &v.bytecode.instrs {
        match ins {
            Instr::LensProj { dst, region, .. } => {
                ptr(region)?;
                if *dst != 0 {
                    bail!("LENS ops must write to dst:0");
                }
            }
            Instr::LensMerge { dst, region, .. } => {
                ptr(region)?;
                if *dst != 0 {
                    bail!("LENS ops must write to dst:0");
                }
            }
            _ => {}
        }
    }
    for p in v
        .expected
        .effect
        .read
        .iter()
        .chain(&v.expected.effect.write)
    {
        ptr(p)?;
    }
    if let Some(inputs) = &v.inputs {
        for k in inputs.keys() {
            ptr(k)?;
        }
    }
    if let Some(d) = &v.expected.delta {
        if *d != Value::Null {
            let first_const0 = v.bytecode.instrs.iter().find(|ins| match ins {
            Instr::Const { dst, .. } if *dst == 0 => true,
            _ => false,
            });
            if first_const0.is_none() {
                bail!("missing CONST dst:0 for initial state");
            }
            let has_lens = v
                .bytecode
                .instrs
                .iter()
                .any(|ins| matches!(ins, Instr::LensProj { .. } | Instr::LensMerge { .. }));
            if !has_lens {
                bail!("expected state change but no LENS_* op found");
            }
        }
    }
    Ok(())
}

fn ensure_no_floats(v: &Value) -> Result<()> {
    match v {
        Value::Number(n) => {
            if n.is_f64() {
                bail!("E_L0_FLOAT: non-integer number found: {}", n);
            }
        }
        Value::Array(arr) => {
            for x in arr {
                ensure_no_floats(x)?;
            }
        }
        Value::Object(map) => {
            for x in map.values() {
                ensure_no_floats(x)?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn to_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        s.push(HEX[(b >> 4) as usize] as char);
        s.push(HEX[(b & 0x0f) as usize] as char);
    }
    s
}

#[test]
fn vectors() -> Result<()> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/vectors");
    let mut files: Vec<_> = fs::read_dir(&dir)?
        .filter_map(|e| {
            let p = e.ok()?.path();
            if p.extension()?.to_str()? == "json" {
                Some(p)
            } else {
                None
            }
        })
        .collect();
    files.sort();

    let mut report: Vec<ReportEntry> = Vec::new();

    for file in files {
        let data = fs::read_to_string(&file)?;
        let raw: Value = serde_json::from_str(&data)?;
        ensure_no_floats(&raw)?;
        let vec: Vector = serde_json::from_value(raw)?;
        lint_vector(&vec)?;

        let host = EffectHost::new(DummyHost);
        let vm = VM { host: &host };
        let run_res = vm.run(&vec.bytecode);
        let (delta, err_msg) = match run_res {
            Ok(d) => (d, None),
            Err(e) => (Value::Null, Some(e.to_string())),
        };
        let effect = host.normalize();
        let journal = host.journal.borrow().clone();

        let mut ok = false;
        if let Some(expected_err) = vec.expected.error.clone() {
            if err_msg.as_deref() == Some(expected_err.as_str()) {
                let exp_eff = canonical_json_bytes(&json!(vec.expected.effect))?;
                let act_eff = canonical_json_bytes(&json!(effect.clone()))?;
                let exp_j = canonical_json_bytes(&json!(vec.expected.journal.clone().unwrap_or_default()))?;
                let act_j = canonical_json_bytes(&json!(journal.clone()))?;
                ok = exp_eff == act_eff && exp_j == act_j;
            }
        } else if err_msg.is_none() {
            let expected_json = json!({
                "delta": vec.expected.delta.clone().unwrap_or(Value::Null),
                "effect": vec.expected.effect,
                "journal": vec.expected.journal.clone().unwrap_or_default()
            });
            let actual_json = json!({
                "delta": delta,
                "effect": effect.clone(),
                "journal": journal.clone()
            });
            ok = canonical_json_bytes(&expected_json)? == canonical_json_bytes(&actual_json)?;
        }

        if ok {
            println!("\u{2713} {}", vec.name);
        } else {
            println!("\u{2717} {}", vec.name);
            if let Some(e) = err_msg { println!("error: {}", e); }
            panic!("vector mismatch");
        }

        let delta_hash = blake3_hex(&canonical_json_bytes(&delta)?);
        let effect_val = serde_json::to_value(&effect)?;
        let effect_hash = blake3_hex(&canonical_json_bytes(&effect_val)?);
        let journal_hash = blake3_hex(&canonical_json_bytes(&json!(journal))?);
        report.push(ReportEntry {
            name: vec.name,
            delta,
            effect,
            delta_hash,
            effect_hash,
            journal: journal.clone(),
            journal_hash,
        });
    }

    let out_dir = dir.join(".out");
    fs::create_dir_all(&out_dir)?;
    let bytes = serde_json::to_vec_pretty(&report)?;
    fs::write(out_dir.join("rs-report.json"), bytes)?;
    Ok(())
}
