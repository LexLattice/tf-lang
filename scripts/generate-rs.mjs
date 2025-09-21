#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { basename, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

export async function generateCrateFromPath(irPath, outDir, packageName) {
  const raw = await readFile(irPath, 'utf8');
  const ir = JSON.parse(raw);
  const resolvedOutDir = resolve(outDir);
  const crateName = packageName || deriveCrateName(ir, resolvedOutDir, irPath);
  await writeCrate(ir, { outDir: resolvedOutDir, packageName: crateName });
  return { outDir: resolvedOutDir, packageName: crateName };
}

export async function writeCrate(ir, { outDir, packageName }) {
  const srcDir = join(outDir, 'src');
  await mkdir(srcDir, { recursive: true });
  await writeFile(join(outDir, 'Cargo.toml'), renderCargoToml(packageName), 'utf8');
  await writeFile(join(srcDir, 'lib.rs'), renderLibRs(), 'utf8');
  await writeFile(join(srcDir, 'adapters.rs'), renderAdaptersRs(), 'utf8');
  await writeFile(join(srcDir, 'pipeline.rs'), renderPipelineRs(), 'utf8');
  await writeFile(join(srcDir, 'run.rs'), renderRunRs(packageName), 'utf8');
  await writeFile(join(srcDir, 'ir.json'), renderIrJson(ir), 'utf8');
}

function deriveCrateName(ir, outDir, irPath) {
  const baseName =
    (ir && typeof ir === 'object' && (ir.name || ir.pipeline?.name || ir.metadata?.name)) ||
    basename(outDir) ||
    basename(irPath).replace(/\.ir\.json$/i, '');
  return sanitizeCrateName(baseName);
}

function sanitizeCrateName(value) {
  const safe = String(value || '')
    .toLowerCase()
    .replace(/[^a-z0-9_\-]/g, '_')
    .replace(/_+/g, '_')
    .replace(/^_+/, '')
    .replace(/_+$/, '');
  return safe || 'tf_generated';
}

function renderCargoToml(packageName) {
  return `[package]\nname = "${packageName}"\nversion = "0.1.0"\nedition = "2021"\nlicense = "MIT OR Apache-2.0"\ndescription = "Generated TF pipeline"\n\n[dependencies]\nanyhow = "1"\nserde = { version = "1", features = ["derive"] }\nserde_json = "1"\nsha2 = "0.10"\n\n[[bin]]\nname = "run"\npath = "src/run.rs"\n`;
}

function renderLibRs() {
  return 'pub mod adapters;\npub mod pipeline;\n\npub use adapters::InMemoryAdapters;\npub use pipeline::{run_pipeline, run_with_ir, TraceEvent};\n';
}

function renderAdaptersRs() {
  return `use std::collections::{HashMap, HashSet};

use anyhow::Result;
use serde::Serialize;
use sha2::{Digest, Sha256};

#[derive(Debug, Clone, Serialize)]
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

impl InMemoryAdapters {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn published(&self) -> &[PublishedMessage] {
        &self.published
    }

    pub fn storage_snapshot(&self) -> HashMap<String, HashMap<String, String>> {
        self.storage.clone()
    }

    pub fn metric_totals(&self) -> HashMap<String, f64> {
        self.metrics.clone()
    }
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

pub trait Observability {
    fn emit_metric(&mut self, name: &str, value: Option<f64>) -> Result<()>;
}

pub trait Crypto {
    fn sign(&mut self, key: &str, data: &[u8]) -> Result<Vec<u8>>;
    fn verify(&mut self, key: &str, data: &[u8], signature: &[u8]) -> Result<bool>;
    fn hash(&mut self, data: &[u8]) -> Result<String>;
}

pub trait AdapterSet: Network + Storage + Observability + Crypto {}

impl<T> AdapterSet for T where T: Network + Storage + Observability + Crypto {}

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
        let token = idempotency_key.map(|tok| format!("{uri}::{key}::{tok}"));
        if let Some(ref id) = token {
            if self.idempotency.contains(id) {
                return Ok(());
            }
        }

        let bucket = self.storage.entry(uri.to_string()).or_insert_with(HashMap::new);
        bucket.insert(key.to_string(), value.to_string());

        if let Some(id) = token {
            self.idempotency.insert(id);
        }

        Ok(())
    }
}

impl Observability for InMemoryAdapters {
    fn emit_metric(&mut self, name: &str, value: Option<f64>) -> Result<()> {
        let increment = value.unwrap_or(1.0);
        let entry = self.metrics.entry(name.to_string()).or_insert(0.0);
        *entry += increment;
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
        Ok(expected.as_slice() == signature)
    }

    fn hash(&mut self, data: &[u8]) -> Result<String> {
        let mut hasher = Sha256::new();
        hasher.update(data);
        let digest = hasher.finalize();
        Ok(to_hex(&digest))
    }
}

fn to_hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write;
        let _ = write!(out, "{:02x}", byte);
    }
    out
}
`;
}

function renderPipelineRs() {
  return `use anyhow::{anyhow, Context, Result};
use serde::Serialize;
use serde_json::{Map, Value};

use crate::adapters::AdapterSet;

const BAKED_IR: &str = include_str!("ir.json");
const CLOCK_START_MS: i64 = 1_690_000_000_000;

#[derive(Debug, Clone, Serialize)]
pub struct TraceEvent {
    pub ts: i64,
    pub prim_id: String,
    pub args: Value,
    pub region: String,
    pub effect: String,
}

pub fn run_pipeline<A>(adapters: &mut A) -> Result<Vec<TraceEvent>>
where
    A: AdapterSet,
{
    let ir: Value = serde_json::from_str(BAKED_IR).context("parsing baked IR JSON")?;
    run_with_ir(&ir, adapters)
}

pub fn run_with_ir<A>(ir: &Value, adapters: &mut A) -> Result<Vec<TraceEvent>>
where
    A: AdapterSet,
{
    let mut ctx = ExecutionContext::new(adapters);
    exec_node(ir, &mut ctx)?;
    Ok(ctx.events)
}

struct ExecutionContext<'a, A> {
    adapters: &'a mut A,
    events: Vec<TraceEvent>,
    clock: Clock,
}

impl<'a, A> ExecutionContext<'a, A>
where
    A: AdapterSet,
{
    fn new(adapters: &'a mut A) -> Self {
        Self {
            adapters,
            events: Vec::new(),
            clock: Clock::new(),
        }
    }

    fn record(&mut self, prim_id: String, args: Value, region: String, effect: String) {
        let ts = self.clock.next();
        self.events.push(TraceEvent {
            ts,
            prim_id,
            args,
            region,
            effect,
        });
    }
}

fn exec_node<A>(node: &Value, ctx: &mut ExecutionContext<A>) -> Result<Value>
where
    A: AdapterSet,
{
    match node.get("node").and_then(Value::as_str) {
        Some("Prim") => exec_prim(node, ctx),
        Some("Seq") | Some("Region") => {
            if let Some(children) = node.get("children").and_then(Value::as_array) {
                for child in children {
                    exec_node(child, ctx)?;
                }
            }
            Ok(Value::Null)
        }
        Some("Par") => {
            if let Some(children) = node.get("children").and_then(Value::as_array) {
                for child in children {
                    exec_node(child, ctx)?;
                }
            }
            Ok(Value::Null)
        }
        _ => {
            if let Some(children) = node.get("children").and_then(Value::as_array) {
                for child in children {
                    exec_node(child, ctx)?;
                }
            }
            Ok(Value::Null)
        }
    }
}

fn exec_prim<A>(node: &Value, ctx: &mut ExecutionContext<A>) -> Result<Value>
where
    A: AdapterSet,
{
    let raw_prim = node
        .get("prim")
        .and_then(Value::as_str)
        .ok_or_else(|| anyhow!("prim node missing prim id"))?;
    let prim_id = canonical_prim(raw_prim).to_string();
    let args_map = normalize_args(node.get("args"));
    let args_value = Value::Object(args_map.clone());
    invoke_primitive(&prim_id, &args_map, ctx)?;

    let region = node
        .get("meta")
        .and_then(|meta| meta.get("region"))
        .and_then(Value::as_str)
        .unwrap_or("")
        .to_string();
    let effect = effect_from_node(node, &prim_id);

    ctx.record(prim_id, args_value, region, effect);
    Ok(Value::Null)
}

fn invoke_primitive<A>(prim_id: &str, args: &Map<String, Value>, ctx: &mut ExecutionContext<A>) -> Result<Value>
where
    A: AdapterSet,
{
    match prim_id {
        "tf:network/publish@1" => {
            let topic = args
                .get("topic")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string();
            let key = args
                .get("key")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string();
            let payload = stringify_payload(args.get("payload"));
            ctx.adapters.publish(&topic, &key, &payload)?;
            Ok(Value::Null)
        }
        "tf:observability/emit-metric@1" => {
            let name = args
                .get("name")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string();
            let value = args.get("value").and_then(Value::as_f64);
            ctx.adapters.emit_metric(&name, value)?;
            Ok(Value::Null)
        }
        "tf:resource/write-object@1" => {
            let uri = args
                .get("uri")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string();
            let key = args
                .get("key")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string();
            let value = stringify_payload(args.get("value"));
            let idempotency_key = args
                .get("idempotency_key")
                .and_then(Value::as_str)
                .or_else(|| args.get("idempotencyKey").and_then(Value::as_str));
            ctx.adapters
                .write_object(&uri, &key, &value, idempotency_key)?;
            Ok(Value::Null)
        }
        "tf:security/sign-data@1" => {
            let key = args
                .get("key")
                .or_else(|| args.get("key_ref"))
                .or_else(|| args.get("keyId"))
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string();
            let payload = stringify_payload(args.get("payload").or_else(|| args.get("value")));
            let _sig = ctx.adapters.sign(&key, payload.as_bytes())?;
            Ok(Value::Null)
        }
        "tf:security/verify-signature@1" => {
            let key = args
                .get("key")
                .or_else(|| args.get("key_ref"))
                .or_else(|| args.get("keyId"))
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string();
            let payload = stringify_payload(args.get("payload").or_else(|| args.get("value")));
            let signature = args
                .get("signature")
                .or_else(|| args.get("sig"))
                .and_then(|value| match value {
                    Value::String(s) => Some(s.as_bytes().to_vec()),
                    Value::Array(items) => {
                        let bytes: Vec<u8> = items
                            .iter()
                            .filter_map(|item| item.as_u64())
                            .map(|byte| byte as u8)
                            .collect();
                        Some(bytes)
                    }
                    _ => None,
                })
                .unwrap_or_default();
            let ok = ctx
                .adapters
                .verify(&key, payload.as_bytes(), &signature)?;
            if !ok {
                return Err(anyhow!("signature verification failed"));
            }
            Ok(Value::Null)
        }
        "tf:information/hash@1" => {
            let target = args
                .get("value")
                .unwrap_or(&Value::Null);
            let canonical = stable_string(target);
            let _digest = ctx.adapters.hash(canonical.as_bytes())?;
            Ok(Value::Null)
        }
        _ => Ok(Value::Null),
    }
}

fn effect_from_node(node: &Value, prim_id: &str) -> String {
    if let Some(Value::String(effect)) = node.get("meta").and_then(|meta| meta.get("effect")).and_then(Value::as_str) {
        return effect.to_string();
    }
    if let Some(Value::Array(effects)) = node.get("meta").and_then(|meta| meta.get("effects")).and_then(Value::as_array) {
        if let Some(effect) = effects.iter().find_map(Value::as_str) {
            return effect.to_string();
        }
    }
    let runtime_effect = effect_for(prim_id);
    if !runtime_effect.is_empty() {
        return runtime_effect.to_string();
    }
    String::new()
}

fn normalize_args(value: Option<&Value>) -> Map<String, Value> {
    match value {
        Some(Value::Object(map)) => map.clone(),
        _ => Map::new(),
    }
}

fn canonical_prim(name: &str) -> &'static str {
    match name {
        "tf:network/publish@1" | "publish" => "tf:network/publish@1",
        "tf:observability/emit-metric@1" | "emit-metric" => "tf:observability/emit-metric@1",
        "tf:resource/write-object@1" | "write-object" => "tf:resource/write-object@1",
        "tf:security/sign-data@1" | "sign-data" => "tf:security/sign-data@1",
        "tf:security/verify-signature@1" | "verify-signature" => "tf:security/verify-signature@1",
        "tf:information/hash@1" | "hash" => "tf:information/hash@1",
        other => other,
    }
}

fn effect_for(prim: &str) -> &'static str {
    match prim {
        "tf:network/publish@1" => "Network.Out",
        "tf:observability/emit-metric@1" => "Observability",
        "tf:resource/write-object@1" => "Storage.Write",
        "tf:security/sign-data@1" => "Crypto",
        "tf:security/verify-signature@1" => "Crypto",
        "tf:information/hash@1" => "Crypto",
        _ => "",
    }
}

fn stringify_payload(value: Option<&Value>) -> String {
    match value {
        Some(Value::String(text)) => text.to_string(),
        Some(other) => stable_string(other),
        None => String::new(),
    }
}

fn stable_string(value: &Value) -> String {
    let canonical = canonical_value(value);
    serde_json::to_string(&canonical).unwrap_or_else(|_| "".to_string())
}

fn canonical_value(value: &Value) -> Value {
    match value {
        Value::Array(items) => {
            let mapped: Vec<Value> = items.iter().map(canonical_value).collect();
            Value::Array(mapped)
        }
        Value::Object(map) => {
            let mut entries: Vec<(&String, &Value)> = map.iter().collect();
            entries.sort_by(|a, b| a.0.cmp(b.0));
            let mut out = Map::new();
            for (key, value) in entries {
                out.insert(key.clone(), canonical_value(value));
            }
            Value::Object(out)
        }
        other => other.clone(),
    }
}

struct Clock {
    base: i64,
    counter: i64,
}

impl Clock {
    fn new() -> Self {
        Self {
            base: CLOCK_START_MS,
            counter: 0,
        }
    }

    fn next(&mut self) -> i64 {
        let ts = self.base + self.counter;
        self.counter += 1;
        ts
    }
}
`;
}

function renderRunRs(packageName) {
  const crateIdent = String(packageName || '').replace(/-/g, '_') || 'tf_generated';
  return `use std::{
    env,
    fs,
    io::{self, Write},
    path::PathBuf,
};

use anyhow::{anyhow, Context, Result};
use ${crateIdent}::{adapters::InMemoryAdapters, pipeline};

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {err:?}");
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    let mut args = env::args().skip(1);
    let mut ir_path: Option<PathBuf> = None;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--ir" => {
                let value = args.next().context("--ir requires a value")?;
                ir_path = Some(PathBuf::from(value));
            }
            "--help" | "-h" => {
                print_usage();
                return Ok(());
            }
            other => return Err(anyhow!("unexpected argument: {other}")),
        }
    }

    let mut adapters = InMemoryAdapters::new();
    let events = if let Some(path) = ir_path {
        let data = fs::read_to_string(&path).context("reading IR file")?;
        let ir: serde_json::Value = serde_json::from_str(&data).context("parsing IR JSON")?;
        pipeline::run_with_ir(&ir, &mut adapters)?
    } else {
        pipeline::run_pipeline(&mut adapters)?
    };

    write_trace(&events)
}

fn write_trace(events: &[pipeline::TraceEvent]) -> Result<()> {
    let trace_path = env::var("TF_TRACE_PATH").ok().map(PathBuf::from);
    if let Some(path) = trace_path {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).context("creating trace directory")?;
        }
        let mut file = fs::File::create(&path).context("creating trace file")?;
        for event in events {
            serde_json::to_writer(&mut file, event).context("serializing trace event")?;
            file.write_all(b"\n").context("writing newline")?;
        }
        return Ok(());
    }

    let stdout = io::stdout();
    let mut handle = stdout.lock();
    for event in events {
        serde_json::to_writer(&mut handle, event).context("serializing trace event")?;
        handle.write_all(b"\n").context("writing newline")?;
    }
    Ok(())
}

fn print_usage() {
    eprintln!("Usage: run [--ir <path>]");
}
`;
}

function canonicalValue(value) {
  if (Array.isArray(value)) {
    return value.map((item) => canonicalValue(item));
  }
  if (value && typeof value === 'object') {
    const entries = Object.entries(value)
      .filter(([, v]) => v !== undefined)
      .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
    const out = {};
    for (const [key, val] of entries) {
      out[key] = canonicalValue(val);
    }
    return out;
  }
  return value;
}

function renderIrJson(ir) {
  const canonical = canonicalValue(ir);
  return `${JSON.stringify(canonical, null, 2)}\n`;
}

async function main() {
  const args = process.argv.slice(2);
  if (args.length === 0 || args.includes('--help') || args.includes('-h')) {
    printUsage();
    return;
  }

  const irPath = args[0];
  let outDir = null;
  let packageName = null;

  for (let i = 1; i < args.length; i += 1) {
    const arg = args[i];
    if (arg === '-o' || arg === '--out' || arg === '--out-dir') {
      i += 1;
      outDir = args[i];
    } else if (arg === '--package-name') {
      i += 1;
      packageName = args[i];
    } else {
      throw new Error(`Unknown argument: ${arg}`);
    }
  }

  if (!irPath) {
    throw new Error('IR path is required');
  }
  if (!outDir) {
    throw new Error('Output directory required via -o or --out');
  }

  await generateCrateFromPath(irPath, outDir, packageName);
  console.log(`wrote ${resolve(outDir)}`);
}

function printUsage() {
  console.log('Usage: node scripts/generate-rs.mjs <ir.json> -o <output dir> [--package-name <name>]');
}

const modulePath = fileURLToPath(new URL(import.meta.url));
if (process.argv[1] === modulePath) {
  main().catch((err) => {
    console.error(err?.stack || err?.message || String(err));
    process.exitCode = 1;
  });
}
