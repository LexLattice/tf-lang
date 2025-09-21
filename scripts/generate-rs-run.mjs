#!/usr/bin/env node
import { dirname, join, resolve } from 'node:path';
import { mkdir } from 'node:fs/promises';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { generateCrateFromPath } from './generate-rs.mjs';

export async function generateAndMaybeRun(irPath, outDir, options = {}) {
  const resolvedOut = resolve(outDir);
  const { packageName } = await generateCrateFromPath(irPath, resolvedOut, options.packageName);

  let tracePath = null;
  if (options.runRust) {
    tracePath = options.tracePath || join(resolvedOut, 'out', 'trace.jsonl');
    await mkdir(dirname(tracePath), { recursive: true });
    await runCargo(resolvedOut, irPath, tracePath, packageName);
  }

  return { outDir: resolvedOut, packageName, tracePath };
}

async function runCargo(crateDir, irPath, tracePath, packageName) {
  const env = { ...process.env, TF_TRACE_PATH: tracePath };
  const args = ['run', '--manifest-path', join(crateDir, 'Cargo.toml'), '--', '--ir', irPath];
  await new Promise((resolvePromise, reject) => {
    const child = spawn('cargo', args, {
      cwd: crateDir,
      stdio: 'inherit',
      env,
    });
    child.on('error', (err) => reject(err));
    child.on('close', (code) => {
      if (code === 0) {
        resolvePromise();
      } else {
        reject(new Error(`cargo run failed (crate ${packageName})`));
      }
    });
  });
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

  const runRust = process.env.LOCAL_RUST === '1';
  const traceOverride = process.env.RUST_TRACE_PATH || null;
  const result = await generateAndMaybeRun(irPath, outDir, {
    packageName,
    runRust,
    tracePath: traceOverride ? resolve(traceOverride) : null,
  });

  console.log(`generated crate ${result.packageName} at ${result.outDir}`);
  if (runRust) {
    console.log(`rust trace written to ${result.tracePath}`);
  } else {
    console.log('skipped rust run (set LOCAL_RUST=1 to enable)');
  }
}

function printUsage() {
  console.log('Usage: node scripts/generate-rs-run.mjs <ir.json> -o <output dir> [--package-name <name>]');
}

const modulePath = fileURLToPath(new URL(import.meta.url));
if (process.argv[1] === modulePath) {
  main().catch((err) => {
    console.error(err?.stack || err?.message || String(err));
    process.exitCode = 1;
  });
}
