#!/usr/bin/env node
import { mkdirSync, writeFileSync, rmSync, readFileSync } from 'node:fs';
import { join, dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import inmem from '../packages/tf-l0-codegen-ts/src/runtime/inmem.mjs';

const __dir = dirname(fileURLToPath(import.meta.url));
const repoRoot = join(__dir, '..');
const baseOutDir = process.env.TF_PILOT_OUT_DIR
  ? resolve(repoRoot, process.env.TF_PILOT_OUT_DIR)
  : join(repoRoot, 'out', '0.4', 'pilot-l0');
const outDir = join(baseOutDir, 'manual');
const statusPath = process.env.TF_STATUS_PATH ?? join(outDir, 'status.json');
const tracePath = process.env.TF_TRACE_PATH ?? join(outDir, 'trace.jsonl');
const summaryPath = join(outDir, 'summary.json');
const deterministicClockEpochMs = 1700000000000n;

function ensureDir(path) {
  mkdirSync(dirname(path), { recursive: true });
}

function safeRm(path) {
  try {
    rmSync(path);
  } catch (err) {
    if (err?.code !== 'ENOENT') throw err;
  }
}

function ensureClock() {
  if (!globalThis.__tf_clock || globalThis.__tf_clock.__pilot_clock !== true) {
    const epochMs = deterministicClockEpochMs;
    let tick = 0n;
    globalThis.__tf_clock = {
      __pilot_clock: true,
      nowNs() {
        const currentMs = epochMs + tick;
        tick += 1n;
        return currentMs * 1_000_000n;
      },
    };
  }
  return () => {
    const ns = globalThis.__tf_clock.nowNs();
    const ms = typeof ns === 'bigint' ? ns / 1_000_000n : BigInt(Math.trunc(ns)) / 1_000_000n;
    return Number(ms);
  };
}

async function callAdapter(primId, args, nextTs, effects, events) {
  const adapter = inmem.getAdapter(primId);
  if (typeof adapter !== 'function') {
    throw new Error(`pilot-handwritten: missing adapter for ${primId}`);
  }
  const ts = nextTs();
  const result = await adapter(args, inmem.state);
  const effect = inmem.effectFor(primId) ?? '';
  if (effect) {
    effects.add(effect);
  }
  events.push({ ts, prim_id: primId, args, region: '', effect });
  return result;
}

async function main() {
  ensureDir(statusPath);
  ensureDir(tracePath);
  ensureDir(summaryPath);
  safeRm(statusPath);
  safeRm(tracePath);
  safeRm(summaryPath);

  if (typeof inmem.reset === 'function') {
    inmem.reset();
  }

  const nextTs = ensureClock();
  const effects = new Set();
  const events = [];

  await callAdapter('tf:observability/emit-metric@1', { name: 'pilot.replay.start' }, nextTs, effects, events);
  await callAdapter('tf:network/publish@1', {
    topic: 'orders',
    key: 'o-1',
    payload: '{"sym":"ABC","side":"buy","qty":1}',
  }, nextTs, effects, events);
  await callAdapter('tf:observability/emit-metric@1', { name: 'pilot.exec.sent' }, nextTs, effects, events);
  await callAdapter('tf:resource/write-object@1', {
    uri: 'res://ledger/pilot',
    key: 'o-1',
    value: 'filled',
  }, nextTs, effects, events);
  await callAdapter('tf:observability/emit-metric@1', { name: 'pilot.ledger.write' }, nextTs, effects, events);

  const status = {
    ok: true,
    ops: events.length,
    effects: Array.from(effects).sort(),
  };

  writeFileSync(statusPath, `${JSON.stringify(status, null, 2)}\n`);

  const traceLines = events.map((entry) => JSON.stringify(entry)).join('\n');
  writeFileSync(tracePath, traceLines ? `${traceLines}\n` : '');

  const traceRaw = readFileSync(tracePath, 'utf8');
  const summary = spawnSync('node', ['packages/tf-l0-tools/trace-summary.mjs'], { input: traceRaw, encoding: 'utf8' });
  if (summary.status !== 0) {
    throw new Error('pilot-handwritten: trace-summary failed');
  }
  const summaryJson = JSON.parse(summary.stdout);
  writeFileSync(summaryPath, `${JSON.stringify(summaryJson)}\n`);

  console.log('pilot-handwritten complete');
}

await main().catch((err) => {
  console.error(err instanceof Error ? err.message : err);
  process.exit(1);
});
