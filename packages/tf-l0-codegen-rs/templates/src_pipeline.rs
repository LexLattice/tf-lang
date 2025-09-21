use std::{
    borrow::Cow,
    collections::BTreeMap,
    fs::OpenOptions,
    io::{BufWriter, Write},
    path::Path,
};

use anyhow::{Context, Result};
use serde::Serialize;
use serde_json::{Map, Value};

use crate::adapters::{Crypto, Network, Observability, Storage};

const CLOCK_START: u64 = 1_690_000_000_000;

pub struct DeterministicClock {
    next: u64,
}

impl DeterministicClock {
    pub fn new() -> Self {
        Self { next: CLOCK_START }
    }

    pub fn tick(&mut self) -> u64 {
        let ts = self.next;
        self.next = self.next.saturating_add(1);
        ts
    }
}

pub struct TraceWriter {
    file: Option<BufWriter<std::fs::File>>,
}

impl TraceWriter {
    pub fn new() -> Result<Self> {
        let path = std::env::var("TF_TRACE_PATH").ok();
        let file = match path {
            Some(path) if !path.is_empty() => {
                let path_ref = Path::new(&path);
                if let Some(parent) = path_ref.parent() {
                    std::fs::create_dir_all(parent)
                        .with_context(|| format!("creating trace directory {}", parent.display()))?;
                }
                let file = OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(path_ref)
                    .with_context(|| format!("opening trace file {}", path))?;
                Some(BufWriter::new(file))
            }
            _ => None,
        };
        Ok(Self { file })
    }

    pub fn emit(&mut self, record: TraceRecord) -> Result<()> {
        let line = serde_json::to_string(&record)?;
        println!("{}", line);
        if let Some(writer) = self.file.as_mut() {
            writer.write_all(line.as_bytes())?;
            writer.write_all(b"\n")?;
            writer.flush()?;
        }
        Ok(())
    }

    pub fn finalize(mut self) -> Result<()> {
        if let Some(writer) = self.file.as_mut() {
            writer.flush()?;
        }
        Ok(())
    }
}

#[derive(Serialize)]
pub struct TraceRecord {
    pub ts: u64,
    pub prim_id: String,
    pub args: Value,
    pub region: String,
    pub effect: String,
}

pub fn run_ir<A>(ir: &Value, adapters: &mut A, trace: &mut TraceWriter, clock: &mut DeterministicClock) -> Result<()>
where
    A: Network + Observability + Storage + Crypto,
{
    exec_node(ir, adapters, trace, clock)
}

fn exec_node<A>(node: &Value, adapters: &mut A, trace: &mut TraceWriter, clock: &mut DeterministicClock) -> Result<()>
where
    A: Network + Observability + Storage + Crypto,
{
    match node {
        Value::Object(map) => {
            let kind = map.get("node").and_then(Value::as_str).unwrap_or_default();
            match kind {
                "Prim" => {
                    handle_prim(map, adapters, trace, clock)?;
                }
                "Seq" | "Region" | "Par" => {
                    if let Some(Value::Array(children)) = map.get("children") {
                        for child in children {
                            exec_node(child, adapters, trace, clock)?;
                        }
                    }
                }
                _ => {
                    if let Some(Value::Array(children)) = map.get("children") {
                        for child in children {
                            exec_node(child, adapters, trace, clock)?;
                        }
                    }
                }
            }
        }
        Value::Array(items) => {
            for item in items {
                exec_node(item, adapters, trace, clock)?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn handle_prim<A>(
    map: &Map<String, Value>,
    adapters: &mut A,
    trace: &mut TraceWriter,
    clock: &mut DeterministicClock,
) -> Result<()>
where
    A: Network + Observability + Storage + Crypto,
{
    let prim_name = map.get("prim").and_then(Value::as_str).unwrap_or_default();
    let info = resolve_primitive(prim_name);
    let mut args_value = map
        .get("args")
        .cloned()
        .unwrap_or_else(|| Value::Object(Map::new()));
    if !matches!(args_value, Value::Object(_)) {
        args_value = Value::Object(Map::new());
    }
    let args_map = match &args_value {
        Value::Object(map) => map,
        _ => unreachable!(),
    };

    let meta = map.get("meta");
    let meta_effect = meta
        .and_then(|value| value.get("effect"))
        .and_then(Value::as_str)
        .map(|s| s.to_string());
    let meta_effects = meta
        .and_then(|value| value.get("effects"))
        .and_then(Value::as_array)
        .and_then(|items| items.iter().find_map(|value| value.as_str().map(|s| s.to_string())));
    let effect = info
        .effect
        .map(|s| s.to_string())
        .or(meta_effect)
        .or(meta_effects)
        .unwrap_or_default();

    let region = meta
        .and_then(|value| value.get("region"))
        .and_then(Value::as_str)
        .unwrap_or_default()
        .to_string();

    match info.kind {
        PrimitiveKind::Publish => {
            let topic = string_arg(args_map, "topic");
            let key = string_arg(args_map, "key");
            let payload = payload_arg(args_map.get("payload"));
            adapters.publish(&topic, &key, &payload)?;
        }
        PrimitiveKind::EmitMetric => {
            let name = string_arg(args_map, "name");
            let value = number_arg(args_map, "value");
            adapters.emit_metric(&name, value)?;
        }
        PrimitiveKind::WriteObject => {
            let uri = string_arg(args_map, "uri");
            let key = string_arg(args_map, "key");
            let value = payload_arg(args_map.get("value"));
            let idempotency_key = args_map
                .get("idempotency_key")
                .or_else(|| args_map.get("idempotencyKey"))
                .and_then(Value::as_str)
                .map(|s| s.to_string());
            adapters.write_object(&uri, &key, &value, idempotency_key.as_deref())?;
        }
        PrimitiveKind::ReadObject => {
            let uri = string_arg(args_map, "uri");
            let key = string_arg(args_map, "key");
            let _ = adapters.read_object(&uri, &key)?;
        }
        PrimitiveKind::CompareAndSwap => {
            let uri = string_arg(args_map, "uri");
            let key = string_arg(args_map, "key");
            let expect = args_map
                .get("expect")
                .or_else(|| args_map.get("ifMatch"))
                .or_else(|| args_map.get("if_match"))
                .map(value_to_string);
            let update = args_map
                .get("value")
                .or_else(|| args_map.get("update"))
                .map(|value| payload_arg(Some(value)))
                .unwrap_or_default();
            let _ = adapters.compare_and_swap(&uri, &key, expect.as_deref(), &update)?;
        }
        PrimitiveKind::SignData => {
            let key_id = args_map
                .get("key")
                .or_else(|| args_map.get("key_ref"))
                .or_else(|| args_map.get("keyId"))
                .map(|value| payload_arg(Some(value)))
                .unwrap_or_default();
            let payload = args_map
                .get("payload")
                .or_else(|| args_map.get("value"))
                .map(|value| to_bytes(value))
                .unwrap_or_default();
            let _ = adapters.sign(&key_id, &payload)?;
        }
        PrimitiveKind::VerifySignature => {
            let key_id = args_map
                .get("key")
                .or_else(|| args_map.get("key_ref"))
                .or_else(|| args_map.get("keyId"))
                .map(|value| payload_arg(Some(value)))
                .unwrap_or_default();
            let payload = args_map
                .get("payload")
                .or_else(|| args_map.get("value"))
                .map(|value| to_bytes(value))
                .unwrap_or_default();
            let signature = args_map
                .get("signature")
                .or_else(|| args_map.get("sig"))
                .map(|value| to_bytes(value))
                .unwrap_or_default();
            let _ = adapters.verify(&key_id, &payload, &signature)?;
        }
        PrimitiveKind::Hash => {
            let target = args_map
                .get("value")
                .cloned()
                .unwrap_or_else(|| Value::Object(args_map.clone()));
            let canonical = canonicalize(&target);
            let serialized = serde_json::to_vec(&canonical)?;
            let _ = adapters.hash(&serialized)?;
        }
        PrimitiveKind::Noop => {}
    }

    trace.emit(TraceRecord {
        ts: clock.tick(),
        prim_id: info.canonical.into_owned(),
        args: args_value,
        region,
        effect,
    })
}

#[derive(Clone, Copy)]
enum PrimitiveKind {
    Publish,
    EmitMetric,
    WriteObject,
    ReadObject,
    CompareAndSwap,
    SignData,
    VerifySignature,
    Hash,
    Noop,
}

struct PrimitiveInfo {
    canonical: Cow<'static, str>,
    effect: Option<&'static str>,
    kind: PrimitiveKind,
}

fn resolve_primitive(name: &str) -> PrimitiveInfo {
    match name {
        "tf:network/publish@1" | "publish" => PrimitiveInfo {
            canonical: Cow::Borrowed("tf:network/publish@1"),
            effect: Some("Network.Out"),
            kind: PrimitiveKind::Publish,
        },
        "tf:observability/emit-metric@1" | "emit-metric" => PrimitiveInfo {
            canonical: Cow::Borrowed("tf:observability/emit-metric@1"),
            effect: Some("Observability"),
            kind: PrimitiveKind::EmitMetric,
        },
        "tf:resource/write-object@1" | "write-object" => PrimitiveInfo {
            canonical: Cow::Borrowed("tf:resource/write-object@1"),
            effect: Some("Storage.Write"),
            kind: PrimitiveKind::WriteObject,
        },
        "tf:resource/read-object@1" | "read-object" => PrimitiveInfo {
            canonical: Cow::Borrowed("tf:resource/read-object@1"),
            effect: Some("Storage.Read"),
            kind: PrimitiveKind::ReadObject,
        },
        "tf:resource/compare-and-swap@1" | "compare-and-swap" => PrimitiveInfo {
            canonical: Cow::Borrowed("tf:resource/compare-and-swap@1"),
            effect: Some("Storage.Write"),
            kind: PrimitiveKind::CompareAndSwap,
        },
        "tf:security/sign-data@1" | "sign-data" => PrimitiveInfo {
            canonical: Cow::Borrowed("tf:security/sign-data@1"),
            effect: Some("Crypto"),
            kind: PrimitiveKind::SignData,
        },
        "tf:security/verify-signature@1" | "verify-signature" => PrimitiveInfo {
            canonical: Cow::Borrowed("tf:security/verify-signature@1"),
            effect: Some("Crypto"),
            kind: PrimitiveKind::VerifySignature,
        },
        "tf:information/hash@1" | "hash" => PrimitiveInfo {
            canonical: Cow::Borrowed("tf:information/hash@1"),
            effect: Some("Crypto"),
            kind: PrimitiveKind::Hash,
        },
        other => PrimitiveInfo {
            canonical: Cow::Owned(other.to_string()),
            effect: None,
            kind: PrimitiveKind::Noop,
        },
    }
}

fn string_arg(map: &Map<String, Value>, key: &str) -> String {
    map.get(key)
        .map(value_to_string)
        .unwrap_or_default()
}

fn payload_arg(value: Option<&Value>) -> String {
    value
        .map(value_to_string)
        .unwrap_or_default()
}

fn number_arg(map: &Map<String, Value>, key: &str) -> Option<f64> {
    map.get(key).and_then(Value::as_f64)
}

fn value_to_string(value: &Value) -> String {
    match value {
        Value::String(s) => s.clone(),
        Value::Number(n) => n.to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Null => String::new(),
        _ => serde_json::to_string(value).unwrap_or_default(),
    }
}

fn to_bytes(value: &Value) -> Vec<u8> {
    match value {
        Value::String(s) => s.clone().into_bytes(),
        Value::Number(n) => n.to_string().into_bytes(),
        Value::Bool(b) => {
            if *b {
                b"true".to_vec()
            } else {
                b"false".to_vec()
            }
        }
        Value::Null => Vec::new(),
        _ => serde_json::to_vec(value).unwrap_or_default(),
    }
}

fn canonicalize(value: &Value) -> Value {
    match value {
        Value::Array(items) => {
            Value::Array(items.iter().map(canonicalize).collect())
        }
        Value::Object(map) => {
            let mut sorted = BTreeMap::new();
            for (key, item) in map.iter() {
                sorted.insert(key.clone(), canonicalize(item));
            }
            let mut out = Map::new();
            for (key, item) in sorted {
                out.insert(key, item);
            }
            Value::Object(out)
        }
        _ => value.clone(),
    }
}
