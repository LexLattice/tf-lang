#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { mkdir, readFile, rm, writeFile, copyFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { basename, dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { deriveCrateName, generateRustCrate, loadIr } from './lib/rust-codegen.mjs';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);
const ROOT = resolve(__dirname, '..');
const OUT_ROOT = join(ROOT, 'out', '0.4');

async function main() {
  const args = process.argv.slice(2);
  if (args.length === 0 || args.includes('--help') || args.includes('-h')) {
    printUsage();
    return;
  }

  const flowPath = resolve(args[0]);
  const flowBase = basename(flowPath).replace(/\.tf$/i, '');
  const irDir = join(OUT_ROOT, 'ir');
  const irPath = join(irDir, `${flowBase}.ir.json`);
  const tsOutDir = join(OUT_ROOT, 'codegen-ts', flowBase);
  const rsOutDir = join(OUT_ROOT, 'codegen-rs', flowBase);
  const parityDir = join(OUT_ROOT, 'parity', 'ts-rs');
  const tsTracePath = join(parityDir, 'trace.ts.jsonl');
  const rsTracePath = join(parityDir, 'trace.rs.jsonl');
  const reportPath = join(parityDir, 'report.json');
  const capsPath = join(ROOT, 'tests', 'fixtures', 'caps-observability.json');

  await mkdir(irDir, { recursive: true });
  await mkdir(join(OUT_ROOT, 'codegen-ts'), { recursive: true });
  await mkdir(join(OUT_ROOT, 'codegen-rs'), { recursive: true });
  await mkdir(parityDir, { recursive: true });

  runNode([
    'packages/tf-compose/bin/tf.mjs',
    'parse',
    flowPath,
    '-o',
    irPath,
  ]);

  const ir = await loadIr(irPath);
  const crateName = deriveCrateName(ir, rsOutDir, irPath);
  await generateRustCrate(ir, rsOutDir, crateName);

  await rm(tsOutDir, { recursive: true, force: true });
  runNode([
    'packages/tf-compose/bin/tf.mjs',
    'emit',
    '--lang',
    'ts',
    flowPath,
    '--out',
    tsOutDir,
  ]);

  await runTsRunner(tsOutDir, capsPath, tsTracePath);

  const rustRan = process.env.LOCAL_RUST === '1';
  let rustTraceSource = null;
  if (rustRan) {
    const manifestPath = join(rsOutDir, 'Cargo.toml');
    const cargoArgs = ['run', '--manifest-path', manifestPath, '--', '--ir', irPath];
    const result = spawnSync('cargo', cargoArgs, {
      cwd: rsOutDir,
      stdio: 'inherit',
      env: process.env,
    });
    if (result.status !== 0) {
      throw new Error(`cargo run failed with status ${result.status}`);
    }
    rustTraceSource = join(rsOutDir, 'out', 'trace.jsonl');
    if (existsSync(rustTraceSource)) {
      await copyFile(rustTraceSource, rsTracePath);
    }
  } else {
    await writeFile(rsTracePath, '', 'utf8');
  }

  const tsTrace = await loadTrace(tsTracePath);
  const rsTrace = existsSync(rsTracePath) ? await loadTrace(rsTracePath) : [];
  const comparison = compareTraces(tsTrace, rsTrace);
  const report = {
    equal: comparison.equal,
    counts: { ts: tsTrace.length, rs: rsTrace.length },
    diff: comparison.diff,
    ts_trace: tsTracePath,
    rs_trace: rustTraceSource ?? null,
    rust_ran: rustRan,
  };
  await writeFile(reportPath, JSON.stringify(report, null, 2) + '\n', 'utf8');
  console.log(`parity ${comparison.equal ? 'matched' : 'diverged'} (report ${reportPath})`);
}

function runNode(args) {
  const result = spawnSync(process.execPath, args, {
    cwd: ROOT,
    stdio: 'inherit',
  });
  if (result.status !== 0) {
    throw new Error(`command failed: node ${args.join(' ')}`);
  }
}

async function runTsRunner(outDir, capsPath, tracePath) {
  const runPath = join(outDir, 'run.mjs');
  await rm(tracePath, { force: true });
  const env = { ...process.env, TF_TRACE_PATH: tracePath };
  const result = spawnSync(process.execPath, [runPath, '--caps', capsPath], {
    cwd: outDir,
    stdio: 'inherit',
    env,
  });
  if (result.status !== 0) {
    throw new Error('ts runner failed');
  }
}

async function loadTrace(path) {
  if (!existsSync(path)) {
    return [];
  }
  const raw = await readFile(path, 'utf8');
  return raw
    .split('\n')
    .map((line) => line.trim())
    .filter((line) => line.length > 0)
    .map((line) => JSON.parse(line));
}

function compareTraces(tsEntries, rsEntries) {
  const tsSeq = tsEntries.map((entry) => ({ prim_id: entry.prim_id, effect: entry.effect }));
  const rsSeq = rsEntries.map((entry) => ({ prim_id: entry.prim_id, effect: entry.effect }));
  const length = Math.max(tsSeq.length, rsSeq.length);
  for (let i = 0; i < length; i += 1) {
    const ts = tsSeq[i] ?? null;
    const rs = rsSeq[i] ?? null;
    if (!ts || !rs) {
      return { equal: false, diff: { index: i, ts, rs } };
    }
    if (ts.prim_id !== rs.prim_id || ts.effect !== rs.effect) {
      return { equal: false, diff: { index: i, ts, rs } };
    }
  }
  return { equal: true, diff: null };
}

function printUsage() {
  console.log('Usage: node scripts/cross-parity-ts-rs.mjs <flow.tf>');
}

main().catch((err) => {
  console.error(err && err.stack ? err.stack : err);
  process.exitCode = 1;
});
