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

  const [libTemplate, runtimeTemplate, adaptersTemplate, runTemplate] = await Promise.all([
    readTemplate('src_lib.rs'),
    readTemplate('src_runtime.rs'),
    readTemplate('src_adapters.rs'),
    readTemplate('src_bin_run.rs'),
  ]);

  await writeFile(join(resolvedOut, 'Cargo.toml'), renderCargoToml(crateName), 'utf8');
  await writeFile(join(resolvedOut, 'src', 'lib.rs'), libTemplate, 'utf8');
  await writeFile(join(resolvedOut, 'src', 'runtime.rs'), runtimeTemplate, 'utf8');
  await writeFile(join(resolvedOut, 'src', 'adapters.rs'), adaptersTemplate, 'utf8');
  await writeFile(join(resolvedOut, 'src', 'bin', 'run.rs'), runTemplate.replace(/__CRATE_NAME__/g, crateName), 'utf8');
  await writeFile(join(resolvedOut, 'ir.json'), `${JSON.stringify(ir, null, 2)}\n`, 'utf8');

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
  return `[package]\nname = "${crateName}"\nversion = "0.1.0"\nedition = "2021"\nlicense = "MIT OR Apache-2.0"\ndescription = "Generated TF pipeline"\n\n[dependencies]\nanyhow = "1"\nserde = { version = "1", features = ["derive"] }\nserde_json = "1"\nsha2 = "0.10"\nhex = "0.4"\n`;
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
