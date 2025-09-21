#!/usr/bin/env node
import { resolve, join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { deriveCrateName, generateRustCrate, loadIr } from './lib/rust-codegen.mjs';

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

  if (!outDir) {
    throw new Error('Output directory required via -o or --out');
  }

  const resolvedOutDir = resolve(outDir);
  const ir = await loadIr(irPath);
  const crateName = packageName ?? deriveCrateName(ir, resolvedOutDir, irPath);
  await generateRustCrate(ir, resolvedOutDir, crateName);
  console.log(`wrote ${resolvedOutDir} (crate ${crateName})`);

  if (process.env.LOCAL_RUST === '1') {
    const manifestPath = join(resolvedOutDir, 'Cargo.toml');
    const cargoArgs = ['run', '--manifest-path', manifestPath, '--', '--ir', resolve(irPath)];
    console.log(`running cargo ${cargoArgs.join(' ')}`);
    const result = spawnSync('cargo', cargoArgs, { stdio: 'inherit', env: process.env });
    if (result.status !== 0) {
      throw new Error(`cargo run failed with status ${result.status}`);
    }
  }
}

function printUsage() {
  console.log('Usage: node scripts/generate-rs-run.mjs <ir.json> -o <output dir> [--package-name <name>]');
}

main().catch((err) => {
  console.error(err && err.stack ? err.stack : err);
  process.exitCode = 1;
});
