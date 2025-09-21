import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { basename, join, resolve } from 'node:path';

export async function loadIr(irPath) {
  const raw = await readFile(irPath, 'utf8');
  return JSON.parse(raw);
}

export function deriveCrateName(ir, outDir, irPath) {
  const baseName =
    (ir && typeof ir === 'object' && (ir.name || ir.pipeline?.name || ir.metadata?.name)) ||
    basename(outDir) ||
    basename(irPath).replace(/\.ir\.json$/i, '');
  return sanitizeCrateName(baseName);
}

export function sanitizeCrateName(value) {
  const safe = String(value || '')
    .toLowerCase()
    .replace(/[^a-z0-9_]/g, '_')
    .replace(/_+/g, '_')
    .replace(/^_+/, '')
    .replace(/_+$/, '');
  return safe || 'tf_generated';
}

export async function generateRustCrate(ir, outDir, packageName) {
  const resolvedOutDir = resolve(outDir);
  await mkdir(resolvedOutDir, { recursive: true });
  const srcDir = join(resolvedOutDir, 'src');
  await mkdir(srcDir, { recursive: true });

  const canonicalIr = canonicalJson(ir);

  await writeFile(join(resolvedOutDir, 'Cargo.toml'), renderCargoToml(packageName), 'utf8');
  await writeFile(join(srcDir, 'lib.rs'), renderLibRs(), 'utf8');
  await writeFile(join(srcDir, 'adapters.rs'), renderAdaptersRs(), 'utf8');
  await writeFile(join(srcDir, 'pipeline.rs'), renderPipelineRs(canonicalIr), 'utf8');
  await writeFile(join(srcDir, 'run.rs'), renderRunRs(packageName), 'utf8');
}

export function canonicalize(value) {
  if (Array.isArray(value)) {
    return value.map((entry) => canonicalize(entry));
  }
  if (value && typeof value === 'object') {
    const sorted = {};
    for (const key of Object.keys(value).sort()) {
      const canonical = canonicalize(value[key]);
      if (canonical !== undefined) {
        sorted[key] = canonical;
      }
    }
    return sorted;
  }
  return value;
}

export function canonicalJson(value) {
  return JSON.stringify(canonicalize(value));
}

export function renderCargoToml(packageName) {
  return `[
package]
name = "${packageName}"
version = "0.1.0"
edition = "2021"
license = "MIT OR Apache-2.0"
description = "Generated TF pipeline"

[lib]
path = "src/lib.rs"

[[bin]]
name = "run"
path = "src/run.rs"

[dependencies]
anyhow = "1"
serde = { version = "1", features = ["derive"] }
serde_json = "1"
sha2 = "0.10"
`;
}

export function renderLibRs() {
  return `pub mod adapters;
pub mod pipeline;

pub use adapters::{Adapters, InMemoryAdapters};
pub use pipeline::{run_pipeline, TraceRecord};
`;
}

export function renderAdaptersRs() {
  return `use std::collections::{HashMap, HashSet};

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
        let mut hasher = Sha256::new();
        hasher.update(data);
        let digest = hasher.finalize();
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
`;
}

export function renderPipelineRs(irJson) {
  return `use anyhow::{anyhow, Result};
use serde_json::{Map, Value};

use crate::adapters::Adapters;

#[derive(Debug, Clone, PartialEq)]
pub struct TraceRecord {
    pub ts: u64,
    pub prim_id: String,
    pub args: Value,
    pub region: String,
    pub effect: String,
}

pub fn baked_ir() -> &'static str {
    ${renderStaticStr(irJson)}
}

pub fn run_pipeline<A, F>(adapters: &mut A, ir: &Value, emit: &mut F) -> Result<()>
where
    A: ?Sized + Adapters,
    F: FnMut(TraceRecord) -> Result<()>,
{
    let mut ctx = ExecContext::new();
    exec_node(ir, adapters, emit, &mut ctx, None)?;
    Ok(())
}

#[derive(Debug, Default)]
struct ExecContext {
    clock: Clock,
}

impl ExecContext {
    fn new() -> Self {
        Self { clock: Clock::new() }
    }

    fn next_ts(&mut self) -> u64 {
        self.clock.next()
    }
}

#[derive(Debug, Default)]
struct Clock {
    value: u64,
}

impl Clock {
    fn new() -> Self {
        Self { value: 1_690_000_000_000 }
    }

    fn next(&mut self) -> u64 {
        let current = self.value;
        self.value = self.value.saturating_add(1);
        current
    }
}

fn exec_node<A, F>(
    node: &Value,
    adapters: &mut A,
    emit: &mut F,
    ctx: &mut ExecContext,
    region: Option<&str>,
) -> Result<Value>
where
    A: ?Sized + Adapters,
    F: FnMut(TraceRecord) -> Result<()>,
{
    let kind = node.get("node").and_then(Value::as_str).unwrap_or("");
    match kind {
        "Prim" => exec_prim(node, adapters, emit, ctx, region),
        "Seq" | "Region" => {
            let mut last = Value::Null;
            let children = node.get("children").and_then(Value::as_array).cloned().unwrap_or_default();
            let next_region = if kind == "Region" {
                node.get("kind").and_then(Value::as_str).map(|value| value.to_string())
            } else {
                region.map(|value| value.to_string())
            };
            for child in children {
                last = exec_node(&child, adapters, emit, ctx, next_region.as_deref())?;
            }
            Ok(last)
        }
        _ => Ok(Value::Null),
    }
}

fn exec_prim<A, F>(
    node: &Value,
    adapters: &mut A,
    emit: &mut F,
    ctx: &mut ExecContext,
    region: Option<&str>,
) -> Result<Value>
where
    A: ?Sized + Adapters,
    F: FnMut(TraceRecord) -> Result<()>,
{
    let name = node.get("prim").and_then(Value::as_str).ok_or_else(|| anyhow!("missing prim name"))?;
    let spec = resolve_primitive(name)?;
    let args = node.get("args").cloned().unwrap_or_else(|| Value::Object(Map::new()));
    let ts = ctx.next_ts();
    let record = TraceRecord {
        ts,
        prim_id: spec.canonical.to_string(),
        args: args.clone(),
        region: region.unwrap_or("").to_string(),
        effect: spec.effect.to_string(),
    };
    emit(record)?;
    execute_primitive(spec.kind, &args, adapters)
}

enum PrimitiveKind {
    Publish,
    EmitMetric,
    WriteObject,
    ReadObject,
    CompareAndSwap,
    SignData,
    VerifySignature,
    Hash,
    Serialize,
    Deserialize,
}

struct PrimitiveSpec {
    canonical: &'static str,
    effect: &'static str,
    kind: PrimitiveKind,
}

fn resolve_primitive(name: &str) -> Result<PrimitiveSpec> {
    match name {
        "tf:network/publish@1" | "publish" => Ok(PrimitiveSpec {
            canonical: "tf:network/publish@1",
            effect: "Network.Out",
            kind: PrimitiveKind::Publish,
        }),
        "tf:observability/emit-metric@1" | "emit-metric" => Ok(PrimitiveSpec {
            canonical: "tf:observability/emit-metric@1",
            effect: "Observability",
            kind: PrimitiveKind::EmitMetric,
        }),
        "tf:resource/write-object@1" | "write-object" => Ok(PrimitiveSpec {
            canonical: "tf:resource/write-object@1",
            effect: "Storage.Write",
            kind: PrimitiveKind::WriteObject,
        }),
        "tf:resource/read-object@1" | "read-object" => Ok(PrimitiveSpec {
            canonical: "tf:resource/read-object@1",
            effect: "Storage.Read",
            kind: PrimitiveKind::ReadObject,
        }),
        "tf:resource/compare-and-swap@1" | "compare-and-swap" => Ok(PrimitiveSpec {
            canonical: "tf:resource/compare-and-swap@1",
            effect: "Storage.Write",
            kind: PrimitiveKind::CompareAndSwap,
        }),
        "tf:security/sign-data@1" | "sign-data" => Ok(PrimitiveSpec {
            canonical: "tf:security/sign-data@1",
            effect: "Crypto",
            kind: PrimitiveKind::SignData,
        }),
        "tf:security/verify-signature@1" | "verify-signature" => Ok(PrimitiveSpec {
            canonical: "tf:security/verify-signature@1",
            effect: "Crypto",
            kind: PrimitiveKind::VerifySignature,
        }),
        "tf:information/hash@1" | "hash" => Ok(PrimitiveSpec {
            canonical: "tf:information/hash@1",
            effect: "Crypto",
            kind: PrimitiveKind::Hash,
        }),
        "tf:information/serialize@1" | "serialize" => Ok(PrimitiveSpec {
            canonical: "tf:information/serialize@1",
            effect: "Pure",
            kind: PrimitiveKind::Serialize,
        }),
        "tf:information/deserialize@1" | "deserialize" => Ok(PrimitiveSpec {
            canonical: "tf:information/deserialize@1",
            effect: "Pure",
            kind: PrimitiveKind::Deserialize,
        }),
        other => Err(anyhow!("unsupported primitive: {other}")),
    }
}

fn execute_primitive<A>(kind: PrimitiveKind, args: &Value, adapters: &mut A) -> Result<Value>
where
    A: ?Sized + Adapters,
{
    match kind {
        PrimitiveKind::Publish => {
            let topic = value_to_string(args.get("topic"));
            let key = value_to_string(args.get("key"));
            let payload = match args.get("payload") {
                Some(Value::String(s)) => s.clone(),
                Some(value) => value.to_string(),
                None => String::new(),
            };
            adapters.publish(&topic, &key, &payload)?;
            Ok(Value::Null)
        }
        PrimitiveKind::EmitMetric => {
            let name = value_to_string(args.get("name"));
            let value = args.get("value").and_then(Value::as_f64);
            adapters.emit_metric(&name, value)?;
            Ok(Value::Null)
        }
        PrimitiveKind::WriteObject => {
            let uri = value_to_string(args.get("uri"));
            let key = value_to_string(args.get("key"));
            let value = match args.get("value") {
                Some(Value::String(s)) => s.clone(),
                Some(other) => other.to_string(),
                None => String::new(),
            };
            let idempotency = args
                .get("idempotency_key")
                .or_else(|| args.get("idempotencyKey"))
                .and_then(Value::as_str);
            adapters.write_object(&uri, &key, &value, idempotency)?;
            Ok(Value::Null)
        }
        PrimitiveKind::ReadObject => Ok(Value::Null),
        PrimitiveKind::CompareAndSwap => Ok(Value::Null),
        PrimitiveKind::SignData => {
            let key = value_to_string(args.get("key"));
            let payload = args.get("payload").cloned().unwrap_or(Value::Null);
            let bytes = value_to_bytes(&payload);
            let _ = adapters.sign(&key, &bytes)?;
            Ok(Value::Null)
        }
        PrimitiveKind::VerifySignature => {
            let key = value_to_string(args.get("key"));
            let payload = args.get("payload").cloned().unwrap_or(Value::Null);
            let signature = args
                .get("signature")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string();
            let bytes = value_to_bytes(&payload);
            let _ = adapters.verify(&key, &bytes, signature.as_bytes())?;
            Ok(Value::Null)
        }
        PrimitiveKind::Hash => {
            let target = args.get("value").cloned().unwrap_or_else(|| args.clone());
            let data = value_to_bytes(&target);
            let digest = adapters.hash(&data)?;
            Ok(Value::String(digest))
        }
        PrimitiveKind::Serialize => Ok(Value::String(args.to_string())),
        PrimitiveKind::Deserialize => Ok(args.clone()),
    }
}

fn value_to_string(value: Option<&Value>) -> String {
    match value {
        Some(Value::String(s)) => s.clone(),
        Some(other) => other.to_string(),
        None => String::new(),
    }
}

fn value_to_bytes(value: &Value) -> Vec<u8> {
    match value {
        Value::String(s) => s.as_bytes().to_vec(),
        _ => serde_json::to_vec(value).unwrap_or_default(),
    }
}
`;
}

function renderStaticStr(value) {
  const escaped = value.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
  return `"${escaped}"`;
}

export function renderRunRs(packageName) {
  return `use std::{env, fs, io::Write, path::PathBuf};
use std::fs::File;
use std::io::BufWriter;

use anyhow::{anyhow, Context, Result};
use serde_json::Value;

use ${packageName}::adapters::InMemoryAdapters;
use ${packageName}::pipeline::{self, TraceRecord};

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {err}");
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    let mut args = env::args().skip(1);
    let mut ir_path: Option<PathBuf> = None;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--ir" => {
                let value = args.next().ok_or_else(|| anyhow!("--ir requires a value"))?;
                ir_path = Some(PathBuf::from(value));
            }
            "--help" | "-h" => {
                print_usage();
                return Ok(());
            }
            other => return Err(anyhow!("unexpected argument: {other}")),
        }
    }

    let ir_source = if let Some(path) = ir_path {
        fs::read_to_string(&path).with_context(|| format!("reading IR from {path:?}"))?
    } else {
        pipeline::baked_ir().to_string()
    };

    let ir: Value = serde_json::from_str(&ir_source).context("parsing IR JSON")?;
    let mut adapters = InMemoryAdapters::default();

    let trace_path = env::var("TF_TRACE_PATH")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from("out/trace.jsonl"));
    let mut emitter = TraceEmitter::new(trace_path)?;

    pipeline::run_pipeline(&mut adapters, &ir, &mut |record| emitter.emit(record))?;
    emitter.flush()?;
    Ok(())
}

fn print_usage() {
    eprintln!("Usage: run [--ir <path>]");
}

struct TraceEmitter {
    writer: BufWriter<File>,
}

impl TraceEmitter {
    fn new(path: PathBuf) -> Result<Self> {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).with_context(|| format!("creating trace directory {parent:?}"))?;
        }
        let file = File::create(&path).with_context(|| format!("opening trace file {path:?}"))?;
        Ok(Self {
            writer: BufWriter::new(file),
        })
    }

    fn emit(&mut self, record: TraceRecord) -> Result<()> {
        let mut line = String::new();
        line.push('{');
        line.push_str("\"ts\":");
        line.push_str(&record.ts.to_string());
        line.push_str(",\"prim_id\":");
        line.push_str(&serde_json::to_string(&record.prim_id)?);
        line.push_str(",\"args\":");
        line.push_str(&serde_json::to_string(&record.args)?);
        line.push_str(",\"region\":");
        line.push_str(&serde_json::to_string(&record.region)?);
        line.push_str(",\"effect\":");
        line.push_str(&serde_json::to_string(&record.effect)?);
        line.push('}');
        line.push('\n');
        self.writer.write_all(line.as_bytes()).context("writing trace entry")?
    }

    fn flush(&mut self) -> Result<()> {
        self.writer.flush().context("flushing trace writer")
    }
}
`;
}
