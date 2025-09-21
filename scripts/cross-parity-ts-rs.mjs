#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import fs from 'node:fs';
import { basename, dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

import runIRDefault, { runIR as runIRNamed } from '../packages/tf-l0-codegen-ts/src/runtime/run-ir.mjs';
import { createInmemRuntime } from '../packages/tf-l0-codegen-ts/src/runtime/inmem.mjs';

const runIR = runIRNamed ?? runIRDefault;
const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const TF_CLI = join(ROOT, 'packages', 'tf-compose', 'bin', 'tf.mjs');
const GENERATE_SCRIPT = join(ROOT, 'scripts', 'generate-rs-run.mjs');

async function main() {
  const args = process.argv.slice(2);
  if (args.length === 0 || args[0] === '--help' || args[0] === '-h') {
    printUsage();
    return;
  }

  const tfPath = resolve(args[0]);
  const baseName = basename(tfPath).replace(/\.tf$/i, '');
  const irPath = join(ROOT, 'out/0.4/ir', `${baseName}.ir.json`);
  const codegenDir = join(ROOT, 'out/0.4/codegen-rs', baseName);
  const parityDir = join(ROOT, 'out/0.4/parity/ts-rs');

  await mkdir(dirname(irPath), { recursive: true });
  await mkdir(codegenDir, { recursive: true });
  await mkdir(parityDir, { recursive: true });

  ensureIr(tfPath, irPath);
  generateRust(irPath, codegenDir);

  const traceTsPath = join(parityDir, 'trace.ts.jsonl');
  const traceRsPath = join(parityDir, 'trace.rs.jsonl');

  await runTsTrace(irPath, traceTsPath);

  let rustTrace = null;
  let rustPairs = null;
  const rustEnabled = process.env.LOCAL_RUST === '1';
  if (rustEnabled) {
    runRustTrace(codegenDir, irPath, traceRsPath);
    rustTrace = await readTrace(traceRsPath);
    rustPairs = rustTrace.map((entry) => pickPair(entry));
  } else {
    try { fs.rmSync(traceRsPath, { force: true }); } catch (err) { /* noop */ }
  }

  const tsTrace = await readTrace(traceTsPath);
  const tsPairs = tsTrace.map((entry) => pickPair(entry));

  const comparison = rustEnabled ? comparePairs(tsPairs, rustPairs) : { equal: null, diff: null };

  const report = {
    equal: comparison.equal,
    diff: comparison.diff,
    traces: {
      ts: { path: traceTsPath, count: tsPairs.length },
      rs: rustEnabled ? { path: traceRsPath, count: rustPairs.length } : null,
    },
  };

  await writeFile(join(parityDir, 'report.json'), `${JSON.stringify(report, null, 2)}\n`, 'utf8');
}

function ensureIr(tfPath, irPath) {
  const result = spawnSync(process.execPath, [TF_CLI, 'parse', tfPath, '-o', irPath], {
    cwd: ROOT,
    stdio: 'inherit',
  });
  if (result.status !== 0) {
    process.exit(result.status ?? 1);
  }
}

function generateRust(irPath, outDir) {
  const env = { ...process.env };
  if (env.LOCAL_RUST === '1') {
    env.LOCAL_RUST = '0';
  }
  const result = spawnSync(process.execPath, [GENERATE_SCRIPT, irPath, '-o', outDir], {
    cwd: ROOT,
    stdio: 'inherit',
    env,
  });
  if (result.status !== 0) {
    process.exit(result.status ?? 1);
  }
}

async function runTsTrace(irPath, tracePath) {
  const irRaw = await readFile(irPath, 'utf8');
  const ir = JSON.parse(irRaw);
  const prev = process.env.TF_TRACE_PATH;
  process.env.TF_TRACE_PATH = tracePath;
  try { fs.rmSync(tracePath, { force: true }); } catch (err) { /* noop */ }
  try {
    const runtime = createInmemRuntime();
    await runIR(ir, runtime, {});
  } finally {
    if (prev === undefined) {
      delete process.env.TF_TRACE_PATH;
    } else {
      process.env.TF_TRACE_PATH = prev;
    }
  }
}

function runRustTrace(codegenDir, irPath, tracePath) {
  try { fs.rmSync(tracePath, { force: true }); } catch (err) { /* noop */ }
  const result = spawnSync(
    'cargo',
    ['run', '--manifest-path', join(codegenDir, 'Cargo.toml'), '--', '--ir', irPath],
    {
      cwd: codegenDir,
      stdio: 'inherit',
      env: { ...process.env, TF_TRACE_PATH: tracePath },
    },
  );
  if (result.status !== 0) {
    process.exit(result.status ?? 1);
  }
}

async function readTrace(path) {
  if (!fs.existsSync(path)) {
    return [];
  }
  const raw = await readFile(path, 'utf8');
  return raw
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0)
    .map((line) => JSON.parse(line));
}

function pickPair(entry) {
  return { prim_id: entry.prim_id ?? '', effect: entry.effect ?? '' };
}

function comparePairs(tsPairs, rsPairs) {
  if (!rsPairs) {
    return { equal: null, diff: null };
  }
  if (tsPairs.length !== rsPairs.length) {
    return {
      equal: false,
      diff: { kind: 'length', ts: tsPairs.length, rs: rsPairs.length },
    };
  }
  for (let i = 0; i < tsPairs.length; i += 1) {
    const left = tsPairs[i];
    const right = rsPairs[i];
    if (left.prim_id !== right.prim_id || left.effect !== right.effect) {
      return {
        equal: false,
        diff: { kind: 'mismatch', index: i, ts: left, rs: right },
      };
    }
  }
  return { equal: true, diff: null };
}

function printUsage() {
  console.log('Usage: node scripts/cross-parity-ts-rs.mjs <flow.tf>');
}

main().catch((err) => {
  console.error(err && err.stack ? err.stack : err);
  process.exit(1);
});
