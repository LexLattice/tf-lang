#!/usr/bin/env node
import { readFile, mkdir, writeFile } from 'node:fs/promises';
import { basename, join, resolve } from 'node:path';

async function main() {
  const args = process.argv.slice(2);
  if (args.length === 0 || args.includes('--help') || args.includes('-h')) {
    printUsage();
    return;
  }

  const irPath = args[0];
  if (!irPath) {
    throw new Error('IR path is required');
  }

  let outDir = null;
  for (let i = 1; i < args.length; i += 1) {
    const arg = args[i];
    if (arg === '-o' || arg === '--out' || arg === '--out-dir') {
      i += 1;
      outDir = args[i];
    } else {
      throw new Error(`Unknown argument: ${arg}`);
    }
  }

  if (!outDir) {
    throw new Error('Output directory required via -o or --out');
  }

  const raw = await readFile(irPath, 'utf8');
  const ir = JSON.parse(raw);

  const resolvedOutDir = resolve(outDir);
  await mkdir(resolvedOutDir, { recursive: true });

  const crateName = deriveCrateName(ir, resolvedOutDir, irPath);
  await runGenerator(ir, resolvedOutDir, crateName);
  console.log(`wrote ${resolvedOutDir} (crate ${crateName})`);
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
    .replace(/[^a-z0-9_]/g, '_')
    .replace(/_+/g, '_')
    .replace(/^_+/, '')
    .replace(/_+$/, '');
  return safe || 'tf_generated';
}

async function runGenerator(ir, outDir, packageName) {
  const srcDir = join(outDir, 'src');
  await mkdir(srcDir, { recursive: true });

  await writeFile(join(outDir, 'Cargo.toml'), renderCargoToml(packageName), 'utf8');
  await writeFile(join(srcDir, 'pipeline.rs'), renderPipeline(ir), 'utf8');
  await writeFile(join(srcDir, 'lib.rs'), renderLibRs(), 'utf8');
}

function renderCargoToml(packageName) {
  return `[package]\nname = "${packageName}"\nversion = "0.1.0"\nedition = "2021"\nlicense = "MIT OR Apache-2.0"\ndescription = "Generated TF pipeline"\n\n[dependencies]\nanyhow = "1"\n`;
}

function renderLibRs() {
  return 'pub mod pipeline;\n\npub use pipeline::run_pipeline;\n';
}

function renderPipeline(ir) {
  const traits = new Set();
  const steps = [];
  collectPrimitives(ir, traits, steps);
  const orderedTraits = Array.from(traits).sort();

  let output = 'use anyhow::Result;\n\n';
  for (const trait of TRAITS) {
    output += trait.definition;
  }

  output += 'pub fn run_pipeline<A>(adapters: &A) -> Result<()>\n';
  output += 'where\n';
  output += '    A: ?Sized';
  for (const name of orderedTraits) {
    output += ` + ${name}`;
  }
  output += ',\n{\n';
  output += '    let _ = adapters;\n';

  for (const step of steps) {
    output += `    ${formatStepComment(step)}\n`;
  }

  output += '    Ok(())\n';
  output += '}\n';
  return output;
}

const TRAITS = [
  {
    name: 'Network',
    definition:
      'pub trait Network {\n    fn publish(&self, topic: &str, key: &str, payload: &str) -> anyhow::Result<()>;\n}\n\n',
    keywords: ['publish'],
  },
  {
    name: 'Observability',
    definition:
      'pub trait Observability {\n    fn emit_metric(&self, name: &str) -> anyhow::Result<()>;\n}\n\n',
    keywords: ['emit-metric'],
  },
  {
    name: 'Storage',
    definition:
      'pub trait Storage {\n    fn write_object(&self, uri: &str, key: &str, value: &str) -> anyhow::Result<()>;\n}\n\n',
    keywords: ['write-object', 'delete-object', 'compare-and-swap'],
  },
  {
    name: 'Crypto',
    definition:
      'pub trait Crypto {\n    fn sign(&self, key: &str, data: &[u8]) -> anyhow::Result<Vec<u8>>;\n}\n\n',
    keywords: ['sign-data', 'verify-signature', 'encrypt', 'decrypt'],
  },
];

function collectPrimitives(value, traits, steps) {
  if (Array.isArray(value)) {
    for (const item of value) {
      collectPrimitives(item, traits, steps);
    }
    return;
  }

  if (!value || typeof value !== 'object') {
    return;
  }

  if (value.node === 'Prim' && typeof value.prim === 'string') {
    const traitInfo = traitForPrimitive(value.prim);
    if (traitInfo) {
      traits.add(traitInfo.name);
      steps.push({ prim: value.prim, traitName: traitInfo.name });
    } else {
      steps.push({ prim: value.prim, traitName: null });
    }
  }

  if (Array.isArray(value.children)) {
    for (const child of value.children) {
      collectPrimitives(child, traits, steps);
    }
  }

  const keys = Object.keys(value)
    .filter((key) => key !== 'children')
    .sort();

  for (const key of keys) {
    collectPrimitives(value[key], traits, steps);
  }
}

function traitForPrimitive(name) {
  const base = primitiveBase(name).toLowerCase();
  return TRAITS.find((trait) => trait.keywords.includes(base)) ?? null;
}

function primitiveBase(name) {
  const withoutVersion = String(name).split('@')[0] ?? String(name);
  let candidate = withoutVersion;
  for (const delimiter of ['/', '.', ':']) {
    const index = candidate.lastIndexOf(delimiter);
    if (index !== -1) {
      candidate = candidate.slice(index + 1);
    }
  }
  return candidate;
}

function formatStepComment(step) {
  if (step.traitName) {
    return `// Prim: ${step.prim} (requires ${step.traitName})`;
  }
  return `// Prim: ${step.prim}`;
}

function printUsage() {
  console.log('Usage: node scripts/generate-rs.mjs <ir.json> -o <output dir>');
}

main().catch((err) => {
  console.error(err && err.stack ? err.stack : err);
  process.exit(1);
});
