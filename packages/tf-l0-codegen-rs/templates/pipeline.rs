use anyhow::{anyhow, Context, Result};
use serde_json::{Map, Number, Value};

use crate::adapters::{Crypto, Network, Observability, Storage};

#[derive(Clone, Debug)]
pub struct TraceEntry {
    pub ts: i64,
    pub prim_id: String,
    pub args: Value,
    pub region: String,
    pub effect: String,
}

impl TraceEntry {
    pub fn to_json_value(&self) -> Value {
        let mut map = Map::new();
        map.insert("ts".to_string(), Value::Number(Number::from(self.ts)));
        map.insert("prim_id".to_string(), Value::String(self.prim_id.clone()));
        map.insert("args".to_string(), self.args.clone());
        map.insert("region".to_string(), Value::String(self.region.clone()));
        map.insert("effect".to_string(), Value::String(self.effect.clone()));
        Value::Object(map)
    }
}

struct Clock {
    next: i64,
}

impl Clock {
    fn new() -> Self {
        Self { next: 1_690_000_000_000 }
    }

    fn tick(&mut self) -> i64 {
        let current = self.next;
        self.next += 1;
        current
    }
}

enum PrimitiveKind {
    Publish,
    EmitMetric,
    WriteObject,
    SignData,
    Hash,
    VerifySignature,
}

struct PrimitiveSpec {
    base: &'static str,
    canonical: &'static str,
    effect: &'static str,
    kind: PrimitiveKind,
}

const PRIMITIVES: &[PrimitiveSpec] = &[
    PrimitiveSpec {
        base: "publish",
        canonical: "tf:network/publish@1",
        effect: "Network.Out",
        kind: PrimitiveKind::Publish,
    },
    PrimitiveSpec {
        base: "emit-metric",
        canonical: "tf:observability/emit-metric@1",
        effect: "Observability",
        kind: PrimitiveKind::EmitMetric,
    },
    PrimitiveSpec {
        base: "write-object",
        canonical: "tf:resource/write-object@1",
        effect: "Storage.Write",
        kind: PrimitiveKind::WriteObject,
    },
    PrimitiveSpec {
        base: "sign-data",
        canonical: "tf:security/sign-data@1",
        effect: "Crypto",
        kind: PrimitiveKind::SignData,
    },
    PrimitiveSpec {
        base: "hash",
        canonical: "tf:information/hash@1",
        effect: "Crypto",
        kind: PrimitiveKind::Hash,
    },
    PrimitiveSpec {
        base: "verify-signature",
        canonical: "tf:security/verify-signature@1",
        effect: "Crypto",
        kind: PrimitiveKind::VerifySignature,
    },
];

pub fn run_pipeline<A>(ir: &Value, adapters: &mut A) -> Result<Vec<TraceEntry>>
where
    A: ?Sized + Network + Observability + Storage + Crypto,
{
    let mut runner = Runner::new(adapters);
    runner.exec(ir)?;
    Ok(runner.finish())
}

struct Runner<'a, A> {
    adapters: &'a mut A,
    clock: Clock,
    trace: Vec<TraceEntry>,
}

impl<'a, A> Runner<'a, A>
where
    A: Network + Observability + Storage + Crypto,
{
    fn new(adapters: &'a mut A) -> Self {
        Self {
            adapters,
            clock: Clock::new(),
            trace: Vec::new(),
        }
    }

    fn finish(self) -> Vec<TraceEntry> {
        self.trace
    }

    fn exec(&mut self, node: &Value) -> Result<()> {
        match node {
            Value::Null => Ok(()),
            Value::Array(items) => {
                for item in items {
                    self.exec(item)?;
                }
                Ok(())
            }
            Value::Object(map) => {
                match map.get("node").and_then(Value::as_str) {
                    Some("Prim") => self.exec_prim(map),
                    Some("Seq") | Some("Region") | Some("Authorize") => {
                        if let Some(children) = map.get("children").and_then(Value::as_array) {
                            for child in children {
                                self.exec(child)?;
                            }
                        }
                        Ok(())
                    }
                    Some("Par") => {
                        if let Some(children) = map.get("children").and_then(Value::as_array) {
                            for child in children {
                                self.exec(child)?;
                            }
                        }
                        Ok(())
                    }
                    _ => {
                        if let Some(children) = map.get("children").and_then(Value::as_array) {
                            for child in children {
                                self.exec(child)?;
                            }
                        }
                        Ok(())
                    }
                }
            }
            _ => Ok(()),
        }
    }

    fn exec_prim(&mut self, map: &Map<String, Value>) -> Result<()> {
        let prim = map
            .get("prim")
            .and_then(Value::as_str)
            .context("primitive missing prim identifier")?;
        let spec = resolve_primitive(prim)?;
        let args = map.get("args").cloned().unwrap_or_else(|| Value::Object(Map::new()));
        self.invoke(spec, &args)?;
        let region = extract_region(map);
        let effect = extract_effect(map).unwrap_or_else(|| spec.effect.to_string());
        let entry = TraceEntry {
            ts: self.clock.tick(),
            prim_id: spec.canonical.to_string(),
            args,
            region,
            effect,
        };
        self.trace.push(entry);
        Ok(())
    }

    fn invoke(&mut self, spec: &PrimitiveSpec, args: &Value) -> Result<()> {
        match spec.kind {
            PrimitiveKind::Publish => self.invoke_publish(args),
            PrimitiveKind::EmitMetric => self.invoke_emit_metric(args),
            PrimitiveKind::WriteObject => self.invoke_write_object(args),
            PrimitiveKind::SignData => self.invoke_sign_data(args),
            PrimitiveKind::Hash => self.invoke_hash(args),
            PrimitiveKind::VerifySignature => self.invoke_verify_signature(args),
        }
    }

    fn invoke_publish(&mut self, args: &Value) -> Result<()> {
        let topic = arg_string(args, "topic");
        let key = arg_string(args, "key");
        let payload = arg_payload(args)?;
        self.adapters.publish(&topic, &key, &payload)
    }

    fn invoke_emit_metric(&mut self, args: &Value) -> Result<()> {
        let name = arg_string(args, "name");
        let value = arg_number(args, "value");
        self.adapters.emit_metric(&name, value)
    }

    fn invoke_write_object(&mut self, args: &Value) -> Result<()> {
        let uri = arg_string(args, "uri");
        let key = arg_string(args, "key");
        let value = arg_value_string(args)?;
        let idempotency = arg_optional_string(args, "idempotency_key")
            .or_else(|| arg_optional_string(args, "idempotencyKey"));
        self.adapters
            .write_object(&uri, &key, &value, idempotency.as_deref())
    }

    fn invoke_sign_data(&mut self, args: &Value) -> Result<()> {
        let key_id = arg_string_any(&["key", "key_ref", "keyId"], args);
        let payload = arg_bytes(args, &["payload", "value"])?;
        let _ = self.adapters.sign(&key_id, &payload)?;
        Ok(())
    }

    fn invoke_hash(&mut self, args: &Value) -> Result<()> {
        let target = hash_target(args);
        let canonical = canonicalize_value(&target);
        let serialized = serde_json::to_string(&canonical).context("serializing hash target")?;
        let _ = self.adapters.hash(serialized.as_bytes())?;
        Ok(())
    }

    fn invoke_verify_signature(&mut self, args: &Value) -> Result<()> {
        let key_id = arg_string_any(&["key", "key_ref", "keyId"], args);
        let payload = arg_bytes(args, &["payload", "value"])?;
        let signature = arg_signature(args)?;
        let ok = self
            .adapters
            .verify(&key_id, &payload, &signature)?;
        if !ok {
            return Err(anyhow!("signature verification failed"));
        }
        Ok(())
    }
}

fn resolve_primitive(name: &str) -> Result<&'static PrimitiveSpec> {
    if let Some(spec) = PRIMITIVES.iter().find(|spec| spec.canonical == name) {
        return Ok(spec);
    }
    let base = primitive_base(name);
    PRIMITIVES
        .iter()
        .find(|spec| spec.base == base)
        .ok_or_else(|| anyhow!("unsupported primitive: {name}"))
}

fn primitive_base(name: &str) -> &str {
    let without_version = name.split('@').next().unwrap_or(name);
    let mut candidate = without_version;
    for delimiter in ['/', '.', ':'] {
        if let Some(index) = candidate.rfind(delimiter) {
            candidate = &candidate[index + 1..];
        }
    }
    candidate
}

fn extract_region(map: &Map<String, Value>) -> String {
    map.get("meta")
        .and_then(Value::as_object)
        .and_then(|meta| meta.get("region"))
        .and_then(Value::as_str)
        .unwrap_or("")
        .to_string()
}

fn extract_effect(map: &Map<String, Value>) -> Option<String> {
    let meta = map.get("meta").and_then(Value::as_object)?;
    if let Some(effect) = meta.get("effect").and_then(Value::as_str) {
        return Some(effect.to_string());
    }
    if let Some(effects) = meta.get("effects").and_then(Value::as_array) {
        for entry in effects {
            if let Some(effect) = entry.as_str() {
                if !effect.is_empty() {
                    return Some(effect.to_string());
                }
            }
        }
    }
    None
}

fn args_object(args: &Value) -> Option<&Map<String, Value>> {
    args.as_object()
}

fn arg_value<'a>(args: &'a Value, key: &str) -> Option<&'a Value> {
    args_object(args).and_then(|map| map.get(key))
}

fn arg_string(args: &Value, key: &str) -> String {
    arg_optional_string(args, key).unwrap_or_default()
}

fn arg_optional_string(args: &Value, key: &str) -> Option<String> {
    arg_value(args, key).map(value_to_string)
}

fn arg_string_any(keys: &[&str], args: &Value) -> String {
    for key in keys {
        if let Some(value) = arg_optional_string(args, key) {
            if !value.is_empty() {
                return value;
            }
        }
    }
    String::new()
}

fn arg_payload(args: &Value) -> Result<String> {
    if let Some(value) = arg_value(args, "payload") {
        return value_to_payload(value);
    }
    Ok(String::new())
}

fn arg_value_string(args: &Value) -> Result<String> {
    if let Some(value) = arg_value(args, "value") {
        return value_to_payload(value);
    }
    Ok(String::new())
}

fn value_to_payload(value: &Value) -> Result<String> {
    if let Some(text) = value.as_str() {
        Ok(text.to_string())
    } else {
        Ok(serde_json::to_string(value).context("stringifying payload")?)
    }
}

fn value_to_string(value: &Value) -> String {
    match value {
        Value::String(text) => text.clone(),
        Value::Number(num) => num.to_string(),
        Value::Bool(flag) => flag.to_string(),
        Value::Null => String::new(),
        _ => serde_json::to_string(value).unwrap_or_default(),
    }
}

fn arg_number(args: &Value, key: &str) -> Option<f64> {
    let value = arg_value(args, key)?;
    if let Some(number) = value.as_f64() {
        return Some(number);
    }
    if let Some(int) = value.as_i64() {
        return Some(int as f64);
    }
    if let Some(uint) = value.as_u64() {
        return Some(uint as f64);
    }
    None
}

fn arg_bytes(args: &Value, keys: &[&str]) -> Result<Vec<u8>> {
    for key in keys {
        if let Some(value) = arg_value(args, key) {
            return value_to_bytes(value);
        }
    }
    Ok(Vec::new())
}

fn value_to_bytes(value: &Value) -> Result<Vec<u8>> {
    if let Some(text) = value.as_str() {
        return Ok(text.as_bytes().to_vec());
    }
    if let Some(array) = value.as_array() {
        let mut bytes = Vec::with_capacity(array.len());
        for entry in array {
            let number = entry
                .as_u64()
                .ok_or_else(|| anyhow!("array payload must be numeric"))?;
            if number > 255 {
                return Err(anyhow!("array payload out of range"));
            }
            bytes.push(number as u8);
        }
        return Ok(bytes);
    }
    serde_json::to_vec(value).context("serializing payload bytes")
}

fn arg_signature(args: &Value) -> Result<Vec<u8>> {
    if let Some(value) = arg_value(args, "signature") {
        return signature_to_bytes(value);
    }
    if let Some(value) = arg_value(args, "sig") {
        return signature_to_bytes(value);
    }
    Ok(Vec::new())
}

fn signature_to_bytes(value: &Value) -> Result<Vec<u8>> {
    if let Some(text) = value.as_str() {
        if text.len() % 2 == 0 && text.chars().all(|ch| ch.is_ascii_hexdigit()) {
            let decoded = hex::decode(text).context("decoding hex signature")?;
            return Ok(decoded);
        }
        return Ok(text.as_bytes().to_vec());
    }
    value_to_bytes(value)
}

fn hash_target(args: &Value) -> Value {
    if let Some(value) = arg_value(args, "value") {
        value.clone()
    } else {
        args.clone()
    }
}

fn canonicalize_value(value: &Value) -> Value {
    match value {
        Value::Array(items) => {
            Value::Array(items.iter().map(canonicalize_value).collect())
        }
        Value::Object(map) => {
            let mut entries: Vec<_> = map.iter().collect();
            entries.sort_by(|a, b| a.0.cmp(b.0));
            let mut canonical = Map::new();
            for (key, val) in entries {
                canonical.insert(key.clone(), canonicalize_value(val));
            }
            Value::Object(canonical)
        }
        _ => value.clone(),
    }
}
