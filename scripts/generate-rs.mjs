#!/usr/bin/env node
import { readFile, mkdir } from 'node:fs/promises';
import { basename, dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

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
  const moduleDir = dirname(fileURLToPath(import.meta.url));
  const manifestPath = resolve(moduleDir, '..', 'packages', 'tf-l0-codegen-rs', 'Cargo.toml');

  await new Promise((resolvePromise, rejectPromise) => {
    const child = spawn(
      'cargo',
      [
        'run',
        '--quiet',
        '--manifest-path',
        manifestPath,
        '--bin',
        'generate',
        '--',
        '--out-dir',
        outDir,
        '--package-name',
        packageName,
      ],
      { stdio: ['pipe', 'inherit', 'inherit'] },
    );

    child.on('error', rejectPromise);
    child.on('exit', (code) => {
      if (code === 0) {
        resolvePromise();
      } else {
        rejectPromise(new Error(`cargo run exited with code ${code}`));
      }
    });

    child.stdin.write(JSON.stringify(ir));
    child.stdin.end();
  });
}

function printUsage() {
  console.log('Usage: node scripts/generate-rs.mjs <ir.json> -o <output dir>');
}

main().catch((err) => {
  console.error(err && err.stack ? err.stack : err);
  process.exit(1);
});
