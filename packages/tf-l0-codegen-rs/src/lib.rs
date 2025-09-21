use std::{fs, path::Path};

use anyhow::{Context, Result};
use serde_json::{Map, Value};

pub fn generate_workspace(ir: &Value, out_dir: &Path, package_name: &str) -> Result<()> {
    let sanitized = sanitize_crate_name(package_name);
    fs::create_dir_all(out_dir.join("src")).context("creating src directory")?;

    fs::write(out_dir.join("Cargo.toml"), render_cargo_toml(&sanitized))
        .context("writing Cargo.toml")?;
    fs::write(out_dir.join("src/lib.rs"), render_lib_rs()).context("writing src/lib.rs")?;
    fs::write(out_dir.join("src/adapters.rs"), render_adapters_rs())
        .context("writing src/adapters.rs")?;

    let canonical_ir = canonical_json(ir);
    fs::write(
        out_dir.join("src/pipeline.rs"),
        render_pipeline_rs(&canonical_ir),
    )
    .context("writing src/pipeline.rs")?;
    fs::write(out_dir.join("src/run.rs"), render_run_rs(&sanitized)).context("writing src/run.rs")?;
    Ok(())
}

fn sanitize_crate_name(input: &str) -> String {
    let mut out = String::new();
    let mut last_was_underscore = false;
    for ch in input.chars() {
        let lowered = ch.to_ascii_lowercase();
        let normalized = if lowered.is_ascii_alphanumeric() || lowered == '_' {
            lowered
        } else {
            '_'
        };
        if normalized == '_' {
            if last_was_underscore {
                continue;
            }
            last_was_underscore = true;
            out.push('_');
        } else {
            last_was_underscore = false;
            out.push(normalized);
        }
    }
    let trimmed = out.trim_matches('_').to_string();
    if trimmed.is_empty() {
        "tf_generated".to_string()
    } else {
        trimmed
    }
}

fn canonical_json(value: &Value) -> String {
    serde_json::to_string(&canonicalize(value)).expect("canonical JSON serialization")
}

fn canonicalize(value: &Value) -> Value {
    match value {
        Value::Object(map) => {
            let mut entries: Vec<(&String, &Value)> = map.iter().collect();
            entries.sort_by(|a, b| a.0.cmp(b.0));
            let mut result = Map::new();
            for (key, child) in entries {
                result.insert(key.clone(), canonicalize(child));
            }
            Value::Object(result)
        }
        Value::Array(items) => Value::Array(items.iter().map(canonicalize).collect()),
        other => other.clone(),
    }
}

fn render_cargo_toml(package_name: &str) -> String {
    format!(
        "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\nlicense = \"MIT OR Apache-2.0\"\ndescription = \"Generated TF pipeline\"\n\n[lib]\npath = \"src/lib.rs\"\n\n[[bin]]\nname = \"run\"\npath = \"src/run.rs\"\n\n[dependencies]\nanyhow = \"1\"\nserde = {{ version = \"1\", features = [\"derive\"] }}\nserde_json = \"1\"\nsha2 = \"0.10\"\n",
        name = package_name
    )
}

fn render_lib_rs() -> String {
    "pub mod adapters;\npub mod pipeline;\n\npub use adapters::{Adapters, InMemoryAdapters};\npub use pipeline::{run_pipeline, TraceRecord};\n".to_string()
}

fn render_adapters_rs() -> String {
    r#"use std::collections::{HashMap, HashSet};

use anyhow::Result;
use sha2::{Digest, Sha256};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PublishedMessage {
    pub topic: String,
    pub key: String,
    pub payload: String,
}

#[derive(Debug, Default)]
pub struct InMemoryAdapters {
    published: Vec<PublishedMessage>,
    storage: HashMap<String, HashMap<String, String>>,
    idempotency: HashSet<String>,
    metrics: HashMap<String, f64>,
}

pub trait Network {
    fn publish(&mut self, topic: &str, key: &str, payload: &str) -> Result<()>;
}

pub trait Storage {
    fn write_object(
        &mut self,
        uri: &str,
        key: &str,
        value: &str,
        idempotency_key: Option<&str>,
    ) -> Result<()>;
}

pub trait Crypto {
    fn sign(&mut self, key: &str, data: &[u8]) -> Result<Vec<u8>>;
    fn verify(&mut self, key: &str, data: &[u8], signature: &[u8]) -> Result<bool>;
    fn hash(&mut self, data: &[u8]) -> Result<String>;
}

pub trait Observability {
    fn emit_metric(&mut self, name: &str, value: Option<f64>) -> Result<()>;
}

pub trait Adapters: Network + Storage + Crypto + Observability {}
impl<T> Adapters for T where T: Network + Storage + Crypto + Observability {}

impl InMemoryAdapters {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn published(&self) -> &[PublishedMessage] {
        &self.published
    }

    pub fn metrics(&self) -> &HashMap<String, f64> {
        &self.metrics
    }

    fn idempotency_token(uri: &str, key: &str, token: Option<&str>) -> Option<String> {
        token.map(|value| format!("{uri}:::{key}:::{value}"))
    }
}

impl Network for InMemoryAdapters {
    fn publish(&mut self, topic: &str, key: &str, payload: &str) -> Result<()> {
        self.published.push(PublishedMessage {
            topic: topic.to_string(),
            key: key.to_string(),
            payload: payload.to_string(),
        });
        Ok(())
    }
}

impl Storage for InMemoryAdapters {
    fn write_object(
        &mut self,
        uri: &str,
        key: &str,
        value: &str,
        idempotency_key: Option<&str>,
    ) -> Result<()> {
        if let Some(token) = Self::idempotency_token(uri, key, idempotency_key) {
            if self.idempotency.contains(&token) {
                return Ok(());
            }
            self.idempotency.insert(token);
        }
        let bucket = self.storage.entry(uri.to_string()).or_insert_with(HashMap::new);
        bucket.insert(key.to_string(), value.to_string());
        Ok(())
    }
}

impl Crypto for InMemoryAdapters {
    fn sign(&mut self, key: &str, data: &[u8]) -> Result<Vec<u8>> {
        let mut hasher = Sha256::new();
        hasher.update(key.as_bytes());
        hasher.update(data);
        Ok(hasher.finalize().to_vec())
    }

    fn verify(&mut self, key: &str, data: &[u8], signature: &[u8]) -> Result<bool> {
        let expected = self.sign(key, data)?;
        Ok(expected == signature)
    }

    fn hash(&mut self, data: &[u8]) -> Result<String> {
        let digest = Sha256::new().chain_update(data).finalize();
        Ok(format!("sha256:{}", bytes_to_hex(&digest)))
    }
}

impl Observability for InMemoryAdapters {
    fn emit_metric(&mut self, name: &str, value: Option<f64>) -> Result<()> {
        let delta = value.unwrap_or(1.0);
        let current = self.metrics.entry(name.to_string()).or_insert(0.0);
        *current += delta;
        Ok(())
    }
}

fn bytes_to_hex(data: &[u8]) -> String {
    let mut out = String::with_capacity(data.len() * 2);
    for byte in data {
        out.push_str(&format!("{:02x}", byte));
    }
    out
}
"#
    .to_string()
}

fn render_pipeline_rs(ir_json: &str) -> String {
    format!(
        "use anyhow::{{anyhow, Result}};\nuse serde_json::{{Map, Value}};\n\nuse crate::adapters::Adapters;\n\n#[derive(Debug, Clone, PartialEq)]\npub struct TraceRecord {{\n    pub ts: u64,\n    pub prim_id: String,\n    pub args: Value,\n    pub region: String,\n    pub effect: String,\n}}\n\npub fn baked_ir() -> &'static str {{\n    {}\n}}\n\npub fn run_pipeline<A, F>(adapters: &mut A, ir: &Value, emit: &mut F) -> Result<()>\nwhere\n    A: ?Sized + Adapters,\n    F: FnMut(TraceRecord) -> Result<()>,\n{{\n    let mut ctx = ExecContext::new();\n    exec_node(ir, adapters, emit, &mut ctx, None)?;\n    Ok(())\n}}\n\n#[derive(Debug, Default)]\nstruct ExecContext {{\n    clock: Clock,\n}}\n\nimpl ExecContext {{\n    fn new() -> Self {{\n        Self {{ clock: Clock::new() }}\n    }}\n\n    fn next_ts(&mut self) -> u64 {{\n        self.clock.next()\n    }}\n}}\n\n#[derive(Debug, Default)]\nstruct Clock {{\n    value: u64,\n}}\n\nimpl Clock {{\n    fn new() -> Self {{\n        Self {{ value: 1_690_000_000_000 }}\n    }}\n\n    fn next(&mut self) -> u64 {{\n        let current = self.value;\n        self.value = self.value.saturating_add(1);\n        current\n    }}\n}}\n\nfn exec_node<A, F>(\n    node: &Value,\n    adapters: &mut A,\n    emit: &mut F,\n    ctx: &mut ExecContext,\n    region: Option<&str>,\n) -> Result<Value>\nwhere\n    A: ?Sized + Adapters,\n    F: FnMut(TraceRecord) -> Result<()>,\n{{\n    let kind = node.get(\"node\").and_then(Value::as_str).unwrap_or(\"\");\n    match kind {{\n        \"Prim\" => exec_prim(node, adapters, emit, ctx, region),\n        \"Seq\" | \"Region\" => {{\n            let mut last = Value::Null;\n            let children = node\n                .get(\"children\")\n                .and_then(Value::as_array)\n                .cloned()\n                .unwrap_or_default();\n            let next_region = if kind == \"Region\" {{\n                node.get(\"kind\").and_then(Value::as_str).map(|value| value.to_string())\n            }} else {{\n                region.map(|value| value.to_string())\n            }};\n            for child in children {{\n                last = exec_node(&child, adapters, emit, ctx, next_region.as_deref())?;\n            }}\n            Ok(last)\n        }}\n        _ => Ok(Value::Null),\n    }}\n}}\n\nfn exec_prim<A, F>(\n    node: &Value,\n    adapters: &mut A,\n    emit: &mut F,\n    ctx: &mut ExecContext,\n    region: Option<&str>,\n) -> Result<Value>\nwhere\n    A: ?Sized + Adapters,\n    F: FnMut(TraceRecord) -> Result<()>,\n{{\n    let name = node\n        .get(\"prim\")\n        .and_then(Value::as_str)\n        .ok_or_else(|| anyhow!(\"missing prim name\"))?;\n    let spec = resolve_primitive(name)?;\n    let args = node\n        .get(\"args\")\n        .cloned()\n        .unwrap_or_else(|| Value::Object(Map::new()));\n    let ts = ctx.next_ts();\n    let record = TraceRecord {{\n        ts,\n        prim_id: spec.canonical.to_string(),\n        args: args.clone(),\n        region: region.unwrap_or(\"\").to_string(),\n        effect: spec.effect.to_string(),\n    }};\n    emit(record)?;\n    execute_primitive(spec.kind, &args, adapters)\n}}\n\nenum PrimitiveKind {{\n    Publish,\n    EmitMetric,\n    WriteObject,\n    ReadObject,\n    CompareAndSwap,\n    SignData,\n    VerifySignature,\n    Hash,\n    Serialize,\n    Deserialize,\n}}\n\nstruct PrimitiveSpec {{\n    canonical: &'static str,\n    effect: &'static str,\n    kind: PrimitiveKind,\n}}\n\nfn resolve_primitive(name: &str) -> Result<PrimitiveSpec> {{\n    match name {{\n        \"tf:network/publish@1\" | \"publish\" => Ok(PrimitiveSpec {{\n            canonical: \"tf:network/publish@1\",\n            effect: \"Network.Out\",\n            kind: PrimitiveKind::Publish,\n        }}),\n        \"tf:observability/emit-metric@1\" | \"emit-metric\" => Ok(PrimitiveSpec {{\n            canonical: \"tf:observability/emit-metric@1\",\n            effect: \"Observability\",\n            kind: PrimitiveKind::EmitMetric,\n        }}),\n        \"tf:resource/write-object@1\" | \"write-object\" => Ok(PrimitiveSpec {{\n            canonical: \"tf:resource/write-object@1\",\n            effect: \"Storage.Write\",\n            kind: PrimitiveKind::WriteObject,\n        }}),\n        \"tf:resource/read-object@1\" | \"read-object\" => Ok(PrimitiveSpec {{\n            canonical: \"tf:resource/read-object@1\",\n            effect: \"Storage.Read\",\n            kind: PrimitiveKind::ReadObject,\n        }}),\n        \"tf:resource/compare-and-swap@1\" | \"compare-and-swap\" => Ok(PrimitiveSpec {{\n            canonical: \"tf:resource/compare-and-swap@1\",\n            effect: \"Storage.Write\",\n            kind: PrimitiveKind::CompareAndSwap,\n        }}),\n        \"tf:security/sign-data@1\" | \"sign-data\" => Ok(PrimitiveSpec {{\n            canonical: \"tf:security/sign-data@1\",\n            effect: \"Crypto\",\n            kind: PrimitiveKind::SignData,\n        }}),\n        \"tf:security/verify-signature@1\" | \"verify-signature\" => Ok(PrimitiveSpec {{\n            canonical: \"tf:security/verify-signature@1\",\n            effect: \"Crypto\",\n            kind: PrimitiveKind::VerifySignature,\n        }}),\n        \"tf:information/hash@1\" | \"hash\" => Ok(PrimitiveSpec {{\n            canonical: \"tf:information/hash@1\",\n            effect: \"Crypto\",\n            kind: PrimitiveKind::Hash,\n        }}),\n        \"tf:information/serialize@1\" | \"serialize\" => Ok(PrimitiveSpec {{\n            canonical: \"tf:information/serialize@1\",\n            effect: \"Pure\",\n            kind: PrimitiveKind::Serialize,\n        }}),\n        \"tf:information/deserialize@1\" | \"deserialize\" => Ok(PrimitiveSpec {{\n            canonical: \"tf:information/deserialize@1\",\n            effect: \"Pure\",\n            kind: PrimitiveKind::Deserialize,\n        }}),\n        other => Err(anyhow!("unsupported primitive: {other}")),\n    }}\n}}\n\nfn execute_primitive<A>(kind: PrimitiveKind, args: &Value, adapters: &mut A) -> Result<Value>\nwhere\n    A: ?Sized + Adapters,\n{{\n    match kind {{\n        PrimitiveKind::Publish => {{\n            let topic = value_to_string(args.get(\"topic\"));\n            let key = value_to_string(args.get(\"key\"));\n            let payload = match args.get(\"payload\") {{\n                Some(Value::String(s)) => s.clone(),\n                Some(value) => value.to_string(),\n                None => String::new(),\n            }};\n            adapters.publish(&topic, &key, &payload)?;\n            Ok(Value::Null)\n        }}\n        PrimitiveKind::EmitMetric => {{\n            let name = value_to_string(args.get(\"name\"));\n            let value = args.get(\"value\").and_then(Value::as_f64);\n            adapters.emit_metric(&name, value)?;\n            Ok(Value::Null)\n        }}\n        PrimitiveKind::WriteObject => {{\n            let uri = value_to_string(args.get(\"uri\"));\n            let key = value_to_string(args.get(\"key\"));\n            let value = match args.get(\"value\") {{\n                Some(Value::String(s)) => s.clone(),\n                Some(other) => other.to_string(),\n                None => String::new(),\n            }};\n            let idempotency = args\n                .get(\"idempotency_key\")\n                .or_else(|| args.get(\"idempotencyKey\"))\n                .and_then(Value::as_str);\n            adapters.write_object(&uri, &key, &value, idempotency)?;\n            Ok(Value::Null)\n        }}\n        PrimitiveKind::ReadObject => Ok(Value::Null),\n        PrimitiveKind::CompareAndSwap => Ok(Value::Null),\n        PrimitiveKind::SignData => {{\n            let key = value_to_string(args.get(\"key\"));\n            let payload = args.get(\"payload\").cloned().unwrap_or(Value::Null);\n            let bytes = value_to_bytes(&payload);\n            let _ = adapters.sign(&key, &bytes)?;\n            Ok(Value::Null)\n        }}\n        PrimitiveKind::VerifySignature => {{\n            let key = value_to_string(args.get(\"key\"));\n            let payload = args.get(\"payload\").cloned().unwrap_or(Value::Null);\n            let signature = args\n                .get(\"signature\")\n                .and_then(Value::as_str)\n                .unwrap_or_default()\n                .to_string();\n            let bytes = value_to_bytes(&payload);\n            let _ = adapters.verify(&key, &bytes, signature.as_bytes())?;\n            Ok(Value::Null)\n        }}\n        PrimitiveKind::Hash => {{\n            let target = args.get(\"value\").cloned().unwrap_or_else(|| args.clone());\n            let data = value_to_bytes(&target);\n            let digest = adapters.hash(&data)?;\n            Ok(Value::String(digest))\n        }}\n        PrimitiveKind::Serialize => Ok(Value::String(args.to_string())),\n        PrimitiveKind::Deserialize => Ok(args.clone()),\n    }}\n}}\n\nfn value_to_string(value: Option<&Value>) -> String {{\n    match value {{\n        Some(Value::String(s)) => s.clone(),\n        Some(other) => other.to_string(),\n        None => String::new(),\n    }}\n}}\n\nfn value_to_bytes(value: &Value) -> Vec<u8> {{\n    match value {{\n        Value::String(s) => s.as_bytes().to_vec(),\n        _ => serde_json::to_vec(value).unwrap_or_default(),\n    }}\n}}\n",
        render_static_str(ir_json)
    )
}

fn render_static_str(value: &str) -> String {
    let escaped = value.replace('\', "\\").replace('"', "\\\"");
    format!("\"{}\"", escaped)
}

fn render_run_rs(package_name: &str) -> String {
    format!(
        "use std::{{env, fs, io::Write, path::PathBuf}};\nuse std::fs::File;\nuse std::io::BufWriter;\n\nuse anyhow::{{anyhow, Context, Result}};\nuse serde_json::Value;\n\nuse {crate_name}::adapters::InMemoryAdapters;\nuse {crate_name}::pipeline::{{self, TraceRecord}};\n\nfn main() {{\n    if let Err(err) = run() {{\n        eprintln!(\"error: {{}\", err);\n        std::process::exit(1);\n    }}\n}}\n\nfn run() -> Result<()> {{\n    let mut args = env::args().skip(1);\n    let mut ir_path: Option<PathBuf> = None;\n\n    while let Some(arg) = args.next() {{\n        match arg.as_str() {{\n            \"--ir\" => {{\n                let value = args.next().ok_or_else(|| anyhow!(\"--ir requires a value\"))?;\n                ir_path = Some(PathBuf::from(value));\n            }}\n            \"--help\" | \"-h\" => {{\n                print_usage();\n                return Ok(());\n            }}\n            other => return Err(anyhow!(\"unexpected argument: {{}\", other)),\n        }}\n    }}\n\n    let ir_source = if let Some(path) = ir_path {{\n        fs::read_to_string(&path).with_context(|| format!(\"reading IR from {{:?}}\", path))?\n    }} else {{\n        pipeline::baked_ir().to_string()\n    }};\n\n    let ir: Value = serde_json::from_str(&ir_source).context(\"parsing IR JSON\")?;\n    let mut adapters = InMemoryAdapters::default();\n\n    let trace_path = env::var(\"TF_TRACE_PATH\")\n        .map(PathBuf::from)\n        .unwrap_or_else(|_| PathBuf::from(\"out/trace.jsonl\"));\n    let mut emitter = TraceEmitter::new(trace_path)?;\n\n    pipeline::run_pipeline(&mut adapters, &ir, &mut |record| emitter.emit(record))?;\n    emitter.flush()?;\n    Ok(())\n}}\n\nfn print_usage() {{\n    eprintln!(\"Usage: run [--ir <path>]\");\n}}\n\nstruct TraceEmitter {{\n    writer: BufWriter<File>,\n}}\n\nimpl TraceEmitter {{\n    fn new(path: PathBuf) -> Result<Self> {{\n        if let Some(parent) = path.parent() {{\n            fs::create_dir_all(parent).with_context(|| format!(\"creating trace directory {{:?}}\", parent))?;\n        }}\n        let file = File::create(&path).with_context(|| format!(\"opening trace file {{:?}}\", path))?;\n        Ok(Self {{\n            writer: BufWriter::new(file),\n        }})\n    }}\n\n    fn emit(&mut self, record: TraceRecord) -> Result<()> {{\n        let mut line = String::new();\n        line.push('{{');\n        line.push_str(\"\\\"ts\\\":\");\n        line.push_str(&record.ts.to_string());\n        line.push_str(\",\\\"prim_id\\\":\");\n        line.push_str(&serde_json::to_string(&record.prim_id)?);\n        line.push_str(\",\\\"args\\\":\");\n        line.push_str(&serde_json::to_string(&record.args)?);\n        line.push_str(\",\\\"region\\\":\");\n        line.push_str(&serde_json::to_string(&record.region)?);\n        line.push_str(\",\\\"effect\\\":\");\n        line.push_str(&serde_json::to_string(&record.effect)?);\n        line.push('}}');\n        line.push('\\n');\n        self.writer\n            .write_all(line.as_bytes())\n            .context(\"writing trace entry\")\n    }}\n\n    fn flush(&mut self) -> Result<()> {{\n        self.writer.flush().context(\"flushing trace writer\")\n    }}\n}}\n",
        crate_name = package_name
    )
}
