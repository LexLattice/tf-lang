#!/usr/bin/env node
import { existsSync } from 'node:fs';
import { mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { dirname, join, resolve, basename } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { generateRustCrate } from './generate-rs.mjs';

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(HERE, '..');
const OUT_ROOT = join(ROOT, 'out', '0.4');
const CAP_DEFAULT = {
  effects: ['Network.Out', 'Storage.Write', 'Storage.Read', 'Crypto', 'Observability', 'Pure'],
  allow_writes_prefixes: [''],
};

function printUsage() {
  console.log('Usage: node scripts/cross-parity-ts-rs.mjs <flow.tf>');
}

async function main() {
  const args = process.argv.slice(2);
  if (args.length === 0 || args.includes('--help') || args.includes('-h')) {
    printUsage();
    return;
  }

  const flowPath = resolve(args[0]);
  const flowName = basename(flowPath).replace(/\.tf$/i, '');
  if (!flowName) {
    throw new Error('Unable to derive flow name');
  }

  const irPath = join(OUT_ROOT, 'ir', `${flowName}.ir.json`);
  const tsOutDir = join(OUT_ROOT, 'codegen-ts', flowName);
  const rsOutDir = join(OUT_ROOT, 'codegen-rs', flowName);
  const parityDir = join(OUT_ROOT, 'parity', 'ts-rs');
  const traceTsPath = join(parityDir, 'trace.ts.jsonl');
  const traceRsPath = join(parityDir, 'trace.rs.jsonl');
  const reportPath = join(parityDir, 'report.json');

  await mkdir(parityDir, { recursive: true });

  await emitIr(flowPath, irPath);
  await emitTs(flowPath, tsOutDir);
  await runTsTrace(tsOutDir, traceTsPath);

  await mkdir(rsOutDir, { recursive: true });
  await generateRustCrate(irPath, rsOutDir);

  let rustTrace = [];
  if (process.env.LOCAL_RUST) {
    await runRustTrace(rsOutDir, irPath);
    const produced = join(rsOutDir, 'out', 'trace.jsonl');
    if (existsSync(produced)) {
      const data = await readFile(produced, 'utf8');
      await writeFile(traceRsPath, data, 'utf8');
      rustTrace = parseTracePairs(data);
    }
  } else {
    await rm(traceRsPath, { force: true });
  }

  const tsTraceRaw = existsSync(traceTsPath) ? await readFile(traceTsPath, 'utf8') : '';
  const tsTrace = parseTracePairs(tsTraceRaw);
  if (!rustTrace.length && existsSync(traceRsPath)) {
    const data = await readFile(traceRsPath, 'utf8');
    rustTrace = parseTracePairs(data);
  }

  const comparison = comparePairs(tsTrace, rustTrace);
  const report = {
    equal: comparison.equal,
    diff: comparison.diff,
    counts: { ts: tsTrace.length, rust: rustTrace.length },
    traces: { ts: traceTsPath, rust: traceRsPath },
    flow: flowName,
  };
  await writeFile(reportPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8');
  console.log(`wrote parity report ${reportPath}`);
}

async function emitIr(flowPath, irPath) {
  const result = spawnSync(process.execPath, [
    'packages/tf-compose/bin/tf.mjs',
    'parse',
    flowPath,
    '-o',
    irPath,
  ], {
    cwd: ROOT,
    stdio: 'inherit',
  });
  if (result.status !== 0) {
    throw new Error('tf parse failed');
  }
}

async function emitTs(flowPath, tsOutDir) {
  const result = spawnSync(process.execPath, [
    'packages/tf-compose/bin/tf.mjs',
    'emit',
    '--lang',
    'ts',
    flowPath,
    '--out',
    tsOutDir,
  ], {
    cwd: ROOT,
    stdio: 'inherit',
  });
  if (result.status !== 0) {
    throw new Error('tf emit failed');
  }
}

async function runTsTrace(tsOutDir, tracePath) {
  await rm(tracePath, { force: true });
  const runScript = join(tsOutDir, 'run.mjs');
  const env = {
    ...process.env,
    TF_CAPS: JSON.stringify(CAP_DEFAULT),
    TF_TRACE_PATH: tracePath,
  };
  const result = spawnSync(process.execPath, [runScript], {
    cwd: tsOutDir,
    stdio: 'inherit',
    env,
  });
  if (result.status !== 0) {
    throw new Error('ts run failed');
  }
}

async function runRustTrace(rsOutDir, irPath) {
  const result = spawnSync('cargo', ['run', '--', '--ir', irPath], {
    cwd: rsOutDir,
    stdio: 'inherit',
    env: process.env,
  });
  if (result.status !== 0) {
    throw new Error('rust run failed');
  }
}

function parseTracePairs(raw) {
  if (!raw) return [];
  const lines = raw
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter(Boolean);
  const entries = [];
  for (const line of lines) {
    try {
      const record = JSON.parse(line);
      if (record && typeof record.prim_id === 'string') {
        entries.push({
          prim_id: record.prim_id,
          effect: typeof record.effect === 'string' ? record.effect : '',
        });
      }
    } catch {}
  }
  return entries;
}

function comparePairs(tsPairs, rustPairs) {
  const max = Math.max(tsPairs.length, rustPairs.length);
  for (let i = 0; i < max; i += 1) {
    const tsEntry = tsPairs[i] ?? null;
    const rustEntry = rustPairs[i] ?? null;
    if (!entriesEqual(tsEntry, rustEntry)) {
      return {
        equal: false,
        diff: { index: i, ts: tsEntry, rust: rustEntry },
      };
    }
  }
  return { equal: true, diff: null };
}

function entriesEqual(a, b) {
  if (!a && !b) return true;
  if (!a || !b) return false;
  return a.prim_id === b.prim_id && a.effect === b.effect;
}

main().catch((err) => {
  console.error(err && err.stack ? err.stack : err);
  process.exit(1);
});
