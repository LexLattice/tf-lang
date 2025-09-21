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
const DEFAULT_FLOW = join(ROOT, 'examples', 'flows', 'signing.tf');

async function main() {
  const options = parseArgs(process.argv.slice(2));
  if (options.help) {
    printUsage();
    return;
  }

  const flowPath = resolve(options.flow ?? DEFAULT_FLOW);
  const irPath = resolve(options.ir ?? join(ROOT, 'out/0.4/ir/signing.ir.json'));
  const baseName = deriveBaseName(irPath, flowPath);
  const canonPath = join(dirname(irPath), `${baseName}.canon.json`);
  const codegenDir = join(ROOT, 'out/0.4/codegen-rs', baseName);
  const tracesDir = join(ROOT, 'out/0.4/traces');
  const parityDir = join(ROOT, 'out/0.4/parity/ts-rs');

  await mkdir(dirname(irPath), { recursive: true });
  await mkdir(dirname(canonPath), { recursive: true });
  await mkdir(codegenDir, { recursive: true });
  await mkdir(tracesDir, { recursive: true });
  await mkdir(parityDir, { recursive: true });

  emitIrArtifacts(flowPath, irPath, canonPath);
  generateRust(irPath, codegenDir);

  const traceTsPath = join(tracesDir, 'ts.jsonl');
  const traceRsPath = join(tracesDir, 'rs.jsonl');

  await runTsTrace(irPath, traceTsPath);

  const rustEnabled = process.env.LOCAL_RUST === '1';
  let rustPairs = null;
  if (rustEnabled) {
    runRustTrace(codegenDir, irPath, traceRsPath);
    const rustTrace = await readTrace(traceRsPath);
    rustPairs = rustTrace.map(normalizeTraceEntry);
  } else {
    console.log('LOCAL_RUST != 1; skipping Rust execution and parity check.');
    try { fs.rmSync(traceRsPath, { force: true }); } catch (err) { /* noop */ }
  }

  const tsTrace = await readTrace(traceTsPath);
  const tsPairs = tsTrace.map(normalizeTraceEntry);

  const comparison = rustPairs ? comparePairs(tsPairs, rustPairs) : { equal: null, diff: null };

  const report = {
    equal: comparison.equal,
    diff: comparison.diff,
    traces: {
      ts: { path: traceTsPath, count: tsPairs.length },
      rs: rustPairs ? { path: traceRsPath, count: rustPairs.length } : null,
    },
  };

  await writeFile(join(parityDir, 'report.json'), `${JSON.stringify(report, null, 2)}\n`, 'utf8');
}

function parseArgs(args) {
  const options = { help: false, flow: null, ir: null };
  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i];
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      break;
    } else if (arg === '--flow') {
      i += 1;
      options.flow = args[i];
    } else if (arg === '--ir') {
      i += 1;
      options.ir = args[i];
    } else {
      throw new Error(`Unknown argument: ${arg}`);
    }
  }
  return options;
}

function deriveBaseName(irPath, flowPath) {
  const fromIr = basename(irPath).replace(/\.ir\.json$/i, '');
  if (fromIr.length > 0) return fromIr;
  return basename(flowPath).replace(/\.tf$/i, '');
}

function emitIrArtifacts(flowPath, irPath, canonPath) {
  spawnOrThrow(process.execPath, [TF_CLI, 'parse', flowPath, '-o', irPath]);
  spawnOrThrow(process.execPath, [TF_CLI, 'canon', flowPath, '-o', canonPath]);
}

function generateRust(irPath, outDir) {
  spawnOrThrow(process.execPath, [GENERATE_SCRIPT, irPath, '-o', outDir], { LOCAL_RUST: '0' });
}

async function runTsTrace(irPath, tracePath) {
  const irRaw = await readFile(irPath, 'utf8');
  const ir = JSON.parse(irRaw);
  const prev = process.env.TF_TRACE_PATH;
  process.env.TF_TRACE_PATH = tracePath;
  try { fs.rmSync(tracePath, { force: true }); } catch (err) { /* noop */ }
  try {
    const runtime = createParityRuntime();
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
  spawnOrThrow(
    'cargo',
    ['run', '--manifest-path', join(codegenDir, 'Cargo.toml'), '--', '--ir', irPath],
    { TF_TRACE_PATH: tracePath },
    codegenDir,
  );
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

function normalizeTraceEntry(entry) {
  return {
    prim_id: entry.prim_id ?? '',
    effect: entry.effect ?? '',
  };
}

function createParityRuntime() {
  const runtime = createInmemRuntime();
  const serializeNames = ['serialize', 'tf:information/serialize@1'];
  const serialize = async () => ({ ok: true });

  runtime.adapters = { ...runtime.adapters };
  for (const name of serializeNames) {
    runtime.adapters[name] = serialize;
    runtime[name] = serialize;
  }

  if (typeof runtime.getAdapter === 'function') {
    const base = runtime.getAdapter.bind(runtime);
    runtime.getAdapter = (name) => {
      if (serializeNames.includes(name)) return serialize;
      return base(name);
    };
  }

  if (typeof runtime.effectFor === 'function') {
    const base = runtime.effectFor.bind(runtime);
    runtime.effectFor = (name) => {
      if (serializeNames.includes(name)) return '';
      return base(name);
    };
  }

  return runtime;
}

function comparePairs(tsPairs, rsPairs) {
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

function spawnOrThrow(cmd, args, envOverride = undefined, cwd = ROOT) {
  const result = spawnSync(cmd, args, {
    cwd,
    stdio: 'inherit',
    env: envOverride ? { ...process.env, ...envOverride } : process.env,
  });
  if (result.status !== 0) {
    process.exit(result.status ?? 1);
  }
}

function printUsage() {
  console.log('Usage: node scripts/cross-parity-ts-rs.mjs [--flow <flow.tf>] [--ir <ir.json>]');
}

main().catch((err) => {
  console.error(err && err.stack ? err.stack : err);
  process.exit(1);
});
