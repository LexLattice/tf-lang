#!/usr/bin/env node
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { basename, dirname, join, resolve } from 'node:path';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { generateAndMaybeRun } from './generate-rs-run.mjs';

const here = dirname(fileURLToPath(new URL(import.meta.url)));
const repoRoot = resolve(here, '..');

async function main() {
  const args = process.argv.slice(2);
  if (args.length === 0 || args.includes('--help') || args.includes('-h')) {
    printUsage();
    return;
  }

  const flowPath = resolve(repoRoot, args[0]);
  const flowName = basename(flowPath).replace(/\.tf$/i, '');
  const irPath = args[1] ? resolve(repoRoot, args[1]) : join(repoRoot, 'out', '0.4', 'ir', `${flowName}.ir.json`);
  const tsOutDir = join(repoRoot, 'out', '0.4', 'codegen-ts', flowName);
  const rsOutDir = join(repoRoot, 'out', '0.4', 'codegen-rs', flowName);
  const parityDir = join(repoRoot, 'out', '0.4', 'parity', 'ts-rs');
  const reportPath = join(parityDir, 'report.json');
  const tsTracePath = join(parityDir, 'trace.ts.jsonl');
  const rsTracePath = join(parityDir, 'trace.rs.jsonl');

  await mkdir(parityDir, { recursive: true });

  await ensureIr(flowPath, irPath);
  await emitTs(flowPath, tsOutDir);
  await runTs(tsOutDir, tsTracePath);

  const rustResult = await generateAndMaybeRun(irPath, rsOutDir, {
    runRust: process.env.LOCAL_RUST === '1',
    tracePath: process.env.LOCAL_RUST === '1' ? rsTracePath : null,
  });

  const tsSeq = await loadTrace(tsTracePath);
  const rsSeq = rustResult.tracePath ? await loadTrace(rustResult.tracePath) : null;
  const report = compareSequences(tsSeq, rsSeq);
  report.meta = {
    flow: flowPath,
    ir: irPath,
    tsTrace: tsTracePath,
    rsTrace: rustResult.tracePath,
    rustRan: Boolean(rustResult.tracePath),
  };

  await writeFile(reportPath, `${JSON.stringify(report, null, 2)}\n`);
  if (!report.equal) {
    console.warn('cross-parity: traces differ');
  } else {
    console.log('cross-parity: traces match');
  }
}

async function ensureIr(flowPath, irPath) {
  try {
    await readFile(irPath, 'utf8');
    return;
  } catch {
    await mkdir(dirname(irPath), { recursive: true });
    await runCommand('pnpm', ['run', 'tf', '--', 'parse', flowPath, '-o', irPath]);
  }
}

async function emitTs(flowPath, outDir) {
  await mkdir(outDir, { recursive: true });
  await runCommand('pnpm', ['run', 'tf', '--', 'emit', '--lang', 'ts', flowPath, '--out', outDir]);
}

async function runTs(outDir, tracePath) {
  const traceDir = dirname(tracePath);
  await mkdir(traceDir, { recursive: true });
  const env = {
    ...process.env,
    TF_TRACE_PATH: tracePath,
    TF_CAPS: JSON.stringify({
      effects: ['Network.Out', 'Storage.Write', 'Storage.Read', 'Observability', 'Crypto'],
      allow_writes_prefixes: ['res://', 'mem://'],
    }),
  };
  const runScript = join(outDir, 'run.mjs');
  await runCommand(process.execPath, [runScript], { cwd: outDir, env });
}

async function loadTrace(tracePath) {
  const raw = await readFile(tracePath, 'utf8');
  return raw
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0)
    .map((line) => {
      try {
        const parsed = JSON.parse(line);
        return { prim_id: parsed.prim_id || null, effect: parsed.effect || null };
      } catch {
        return null;
      }
    })
    .filter((entry) => entry && entry.prim_id);
}

function compareSequences(tsSeq, rsSeq) {
  const report = { equal: true, diff: null };
  if (!Array.isArray(tsSeq) || tsSeq.length === 0) {
    report.equal = false;
    report.diff = { reason: 'ts_trace_empty' };
    return report;
  }
  if (!Array.isArray(rsSeq)) {
    report.equal = false;
    report.diff = { reason: 'rust_trace_missing' };
    return report;
  }
  if (tsSeq.length !== rsSeq.length) {
    report.equal = false;
    report.diff = { reason: 'length', ts: tsSeq.length, rust: rsSeq.length };
    return report;
  }
  for (let i = 0; i < tsSeq.length; i += 1) {
    const left = tsSeq[i];
    const right = rsSeq[i];
    if (left.prim_id !== right.prim_id || (left.effect || '') !== (right.effect || '')) {
      report.equal = false;
      report.diff = { index: i, ts: left, rust: right };
      return report;
    }
  }
  return report;
}

function runCommand(cmd, args, options = {}) {
  return new Promise((resolvePromise, reject) => {
    const child = spawn(cmd, args, {
      cwd: repoRoot,
      stdio: 'inherit',
      ...options,
    });
    child.on('error', (err) => reject(err));
    child.on('close', (code) => {
      if (code === 0) {
        resolvePromise();
      } else {
        reject(new Error(`${cmd} ${args.join(' ')} exited with ${code}`));
      }
    });
  });
}

function printUsage() {
  console.log('Usage: node scripts/cross-parity-ts-rs.mjs <flow.tf> [ir.json]');
}

const modulePath = fileURLToPath(new URL(import.meta.url));
if (process.argv[1] === modulePath) {
  main().catch((err) => {
    console.error(err?.stack || err?.message || String(err));
    process.exitCode = 1;
  });
}
