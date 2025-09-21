#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import fs from 'node:fs';
import { basename, dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const TEMPLATE_DIR = join(ROOT, 'packages', 'tf-l0-codegen-rs', 'templates');

async function main() {
  const args = process.argv.slice(2);
  if (args.length === 0 || args.includes('--help') || args.includes('-h')) {
    printUsage();
    return;
  }

  const { irPath, outDir } = parseArgs(args);
  const raw = await readFile(irPath, 'utf8');
  const ir = JSON.parse(raw);

  const resolvedOut = resolve(outDir);
  await mkdir(join(resolvedOut, 'src', 'bin'), { recursive: true });

  const crateName = deriveCrateName(ir, resolvedOut, irPath);

  const [libTemplate, pipelineTemplate, adaptersTemplate, runTemplate] = await Promise.all([
    readTemplate('src_lib.rs'),
    readTemplate('src_pipeline.rs'),
    readTemplate('src_adapters.rs'),
    readTemplate('src_bin_run.rs'),
  ]);

  await writeFile(join(resolvedOut, 'Cargo.toml'), ensureTrailingNewline(renderCargoToml(crateName)), 'utf8');
  await writeFile(join(resolvedOut, 'src', 'lib.rs'), ensureTrailingNewline(libTemplate), 'utf8');
  await writeFile(join(resolvedOut, 'src', 'pipeline.rs'), ensureTrailingNewline(pipelineTemplate), 'utf8');
  await writeFile(join(resolvedOut, 'src', 'adapters.rs'), ensureTrailingNewline(adaptersTemplate), 'utf8');
  const runSource = runTemplate.replace(/__CRATE_NAME__/g, crateName);
  await writeFile(join(resolvedOut, 'src', 'bin', 'run.rs'), ensureTrailingNewline(runSource), 'utf8');
  await writeFile(join(resolvedOut, 'ir.json'), stringifyCanonicalJson(ir), 'utf8');

  console.log(`wrote ${resolvedOut} (crate ${crateName})`);

  if (process.env.LOCAL_RUST === '1') {
    const traceDir = join(resolvedOut, 'out');
    await mkdir(traceDir, { recursive: true });
    const tracePath = join(traceDir, 'trace.jsonl');
    try { fs.rmSync(tracePath, { force: true }); } catch (err) { /* noop */ }
    const result = spawnSync(
      'cargo',
      ['run', '--manifest-path', join(resolvedOut, 'Cargo.toml'), '--', '--ir', irPath],
      {
        cwd: resolvedOut,
        stdio: 'inherit',
        env: { ...process.env, TF_TRACE_PATH: tracePath },
      },
    );
    if (result.status !== 0) {
      process.exit(result.status ?? 1);
    }
  }
}

function parseArgs(args) {
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
  return { irPath, outDir };
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

function renderCargoToml(crateName) {
  const lines = [
    '[package]',
    `name = "${crateName}"`,
    'version = "0.1.0"',
    'edition = "2021"',
    'license = "MIT OR Apache-2.0"',
    'description = "Generated TF pipeline"',
    '',
    '[dependencies]',
    'anyhow = "1"',
    'hex = "0.4"',
    'serde = { version = "1", features = ["derive"] }',
    'serde_json = "1"',
    'sha2 = "0.10"',
  ];
  return lines.join('\n');
}

function stringifyCanonicalJson(value) {
  return `${JSON.stringify(canonicalize(value), null, 2)}\n`;
}

function canonicalize(value) {
  if (Array.isArray(value)) {
    return value.map((entry) => canonicalize(entry));
  }
  if (value && typeof value === 'object' && !Array.isArray(value)) {
    const entries = Object.entries(value)
      .map(([key, child]) => [key, canonicalize(child)])
      .sort(([left], [right]) => left.localeCompare(right));
    return Object.fromEntries(entries);
  }
  return value;
}

function ensureTrailingNewline(content) {
  return content.endsWith('\n') ? content : `${content}\n`;
}

async function readTemplate(file) {
  return readFile(join(TEMPLATE_DIR, file), 'utf8');
}

function printUsage() {
  console.log('Usage: node scripts/generate-rs-run.mjs <ir.json> -o <output dir>');
}

main().catch((err) => {
  console.error(err && err.stack ? err.stack : err);
  process.exit(1);
});
