#!/usr/bin/env node
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { basename, join } from 'node:path';
import { parseArgs } from 'node:util';

const TRAIT_ORDER = ['Kv', 'Crypto', 'Network', 'Observability'];

const TRAIT_DEFINITIONS = {
  Kv: `pub trait Kv {
    fn write_object(&self, uri: &str, key: &str, value: &str) -> anyhow::Result<()>;
    fn read_object(&self, uri: &str, key: &str) -> anyhow::Result<Option<String>>;
    fn delete_object(&self, uri: &str, key: &str) -> anyhow::Result<()>;
    fn compare_and_swap(
        &self,
        uri: &str,
        key: &str,
        expected: Option<&str>,
        value: &str,
    ) -> anyhow::Result<bool>;
}
`,
  Crypto: `pub trait Crypto {
    fn sign(&self, key: &str, data: &[u8]) -> anyhow::Result<Vec<u8>>;
    fn verify(&self, key: &str, signature: &[u8], data: &[u8]) -> anyhow::Result<bool>;
}
`,
  Network: `pub trait Network {
    fn request(&self, uri: &str, payload: &[u8]) -> anyhow::Result<Vec<u8>>;
    fn publish(&self, topic: &str, payload: &[u8]) -> anyhow::Result<()>;
    fn subscribe(&self, topic: &str) -> anyhow::Result<()>;
    fn acknowledge(&self, topic: &str, receipt: &str) -> anyhow::Result<()>;
}
`,
  Observability: `pub trait Observability {
    fn emit_metric(&self, name: &str, value: f64);
}
`,
};

const PRIM_TO_TRAIT = [
  { prefix: 'tf:resource/', trait: 'Kv' },
  { prefix: 'tf:security/', trait: 'Crypto' },
  { prefix: 'tf:network/', trait: 'Network' },
  { prefix: 'tf:observability/', trait: 'Observability' },
];

function parseCli() {
  const { values, positionals } = parseArgs({
    allowPositionals: true,
    options: {
      out: { type: 'string', short: 'o' },
      'crate-name': { type: 'string' },
    },
  });

  if (positionals.length !== 1) {
    throw new Error('IR file path is required as the sole positional argument.');
  }

  const irPath = positionals[0];
  const outDir = values.out;
  if (!outDir) {
    throw new Error('An output directory must be supplied with -o or --out.');
  }

  return {
    irPath,
    outDir,
    crateNameOverride: values['crate-name'] || null,
  };
}

function collectPrimitives(node, out = new Set()) {
  if (!node || typeof node !== 'object') return out;
  if (node.node === 'Prim' && typeof node.prim === 'string') {
    out.add(node.prim);
  }
  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      collectPrimitives(child, out);
    }
  }
  return out;
}

function traitForPrimitive(prim) {
  if (typeof prim !== 'string') return null;
  const lower = prim.toLowerCase();
  if (lower.startsWith('tf:')) {
    const withoutPrefix = lower.slice(3);
    const [domain, remainder = ''] = withoutPrefix.split('/', 2);
    const name = remainder.split('@')[0];
    const fromDomain = traitForDomain(domain);
    if (fromDomain) return fromDomain;
    return traitForShortName(name);
  }
  return traitForShortName(lower);
}

function traitForDomain(domain) {
  const found = PRIM_TO_TRAIT.find((entry) => entry.prefix === `tf:${domain}/`);
  return found ? found.trait : null;
}

function traitForShortName(name) {
  switch (name) {
    case 'write-object':
    case 'read-object':
    case 'delete-object':
    case 'compare-and-swap':
      return 'Kv';
    case 'sign-data':
    case 'verify-signature':
      return 'Crypto';
    case 'request':
    case 'publish':
    case 'subscribe':
    case 'acknowledge':
      return 'Network';
    case 'emit-metric':
      return 'Observability';
    default:
      return null;
  }
}

function sanitizeCrateName(input) {
  let result = '';
  let lastWasSep = true;
  for (const ch of input) {
    if (/^[A-Za-z0-9]$/.test(ch)) {
      result += ch.toLowerCase();
      lastWasSep = false;
    } else if (!lastWasSep && result.length > 0) {
      result += '_';
      lastWasSep = true;
    } else {
      lastWasSep = true;
    }
  }
  while (result.endsWith('_')) {
    result = result.slice(0, -1);
  }
  if (!result) {
    result = 'pipeline';
  }
  if (/^[0-9]/.test(result)) {
    result = `pipeline_${result}`;
  }
  if (['crate', 'self', 'super'].includes(result)) {
    result = `pipeline_${result}`;
  }
  return result;
}

function rustStringLiteral(value) {
  const json = JSON.stringify(value ?? '');
  return json.replace(/\\u2028|\\u2029/g, (match) => {
    if (match === '\\u2028') return '\\u{2028}';
    if (match === '\\u2029') return '\\u{2029}';
    return match;
  });
}

function pipelineNameFromMeta(meta) {
  if (!meta) {
    return null;
  }
  if (typeof meta === 'string' && meta.length > 0) {
    return meta;
  }
  if (typeof meta !== 'object') {
    return null;
  }
  if (typeof meta.name === 'string' && meta.name.length > 0) {
    return meta.name;
  }
  if (typeof meta.id === 'string' && meta.id.length > 0) {
    return meta.id;
  }
  for (const key of ['pipeline', 'info', 'metadata']) {
    if (meta[key]) {
      const nested = pipelineNameFromMeta(meta[key]);
      if (nested) return nested;
    }
  }
  if (Array.isArray(meta)) {
    for (const item of meta) {
      const nested = pipelineNameFromMeta(item);
      if (nested) return nested;
    }
  }
  return null;
}

function determinePipelineName(ir, fallback) {
  if (!ir || typeof ir !== 'object') return fallback;
  const meta = ir.meta;
  const discovered = pipelineNameFromMeta(meta);
  if (typeof discovered === 'string' && discovered.length > 0) {
    return discovered;
  }
  return fallback;
}

function renderCargoToml(crateName) {
  return `[package]
name = "${crateName}"
version = "0.1.0"
edition = "2021"

[dependencies]
anyhow = "1.0"
`;
}

function renderLibRs() {
  return `#![forbid(unsafe_code)]

pub mod pipeline;

pub use pipeline::run_pipeline;
pub use pipeline::PipelineAdapters;
pub use pipeline::PIPELINE_NAME;
pub use pipeline::{Kv, Crypto, Network, Observability};
`;
}

function renderPipelineRs(pipelineName, traitsInUse) {
  const required = TRAIT_ORDER.filter((name) => traitsInUse.has(name));
  const traitBounds = required.length
    ? required.join(' + ')
    : null;
  const header = `//! Auto-generated pipeline scaffolding.

pub const PIPELINE_NAME: &str = ${rustStringLiteral(pipelineName)};

`;
  const traitSection = `${TRAIT_ORDER.map((name) => TRAIT_DEFINITIONS[name]).join('\n')}\n`;
  const adaptersTrait = traitBounds
    ? `pub trait PipelineAdapters: ${traitBounds} {}

impl<T> PipelineAdapters for T where T: ${traitBounds} {}

`
    : `pub trait PipelineAdapters {}

impl<T> PipelineAdapters for T {}

`;
  const body = `pub fn run_pipeline(adapters: &impl PipelineAdapters) -> anyhow::Result<()> {
    let _ = adapters;
    Ok(())
}
`;
  return `${header}${traitSection}${adaptersTrait}${body}`;
}

function mapPrimsToTraits(primitives) {
  const traits = new Set();
  for (const prim of primitives) {
    const traitName = traitForPrimitive(prim);
    if (traitName) traits.add(traitName);
  }
  return traits;
}

async function main() {
  const { irPath, outDir, crateNameOverride } = parseCli();
  const raw = await readFile(irPath, 'utf8');
  const ir = JSON.parse(raw);

  const primitives = collectPrimitives(ir);
  const traits = mapPrimsToTraits(primitives);

  const baseName = crateNameOverride || basename(outDir);
  const crateName = sanitizeCrateName(baseName);
  const pipelineName = determinePipelineName(ir, crateName.replace(/_/g, '-'));

  const cargoToml = renderCargoToml(crateName);
  const libRs = renderLibRs();
  const pipelineRs = renderPipelineRs(pipelineName, traits);

  await mkdir(join(outDir, 'src'), { recursive: true });
  await writeFile(join(outDir, 'Cargo.toml'), cargoToml, 'utf8');
  await writeFile(join(outDir, 'src', 'lib.rs'), libRs, 'utf8');
  await writeFile(join(outDir, 'src', 'pipeline.rs'), pipelineRs, 'utf8');
}

main().catch((err) => {
  console.error(err instanceof Error ? err.message : err);
  process.exitCode = 1;
});
