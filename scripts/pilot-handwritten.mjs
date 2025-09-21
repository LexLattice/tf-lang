#!/usr/bin/env node
import { mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import inmem from '../packages/tf-l0-codegen-ts/src/runtime/inmem.mjs';

const __dirname = dirname(fileURLToPath(import.meta.url));
const repoRoot = join(__dirname, '..');
const pilotOutRel = process.env.TF_PILOT_OUT_DIR ?? 'out/0.4/pilot-l0';
const pilotOut = join(repoRoot, pilotOutRel);
const manualOut = join(pilotOut, 'manual');
const statusPath = join(manualOut, 'status.json');
const tracePath = join(manualOut, 'trace.jsonl');
const summaryPath = join(manualOut, 'summary.json');
const manifestPath = join(pilotOut, 'pilot_min.manifest.json');
const traceSummaryBinary = join(repoRoot, 'packages', 'tf-l0-tools', 'trace-summary.mjs');

mkdirSync(manualOut, { recursive: true });

process.env.TF_STATUS_PATH = statusPath;
process.env.TF_TRACE_PATH = tracePath;

for (const path of [statusPath, tracePath, summaryPath]) {
  try {
    rmSync(path);
  } catch (err) {
    if (err?.code !== 'ENOENT') throw err;
  }
}

const clockBaseMs = 1690000000000n;
let clockCounter = 0n;

function nextTimestampMs() {
  const value = clockBaseMs + clockCounter;
  clockCounter += 1n;
  return Number(value);
}

function recordEffect(set, effect) {
  if (typeof effect === 'string' && effect.length > 0) {
    set.add(effect);
  }
}

async function runManual() {
  if (typeof inmem.reset === 'function') {
    inmem.reset();
  }
  const effects = new Set();
  const events = [];

  async function invoke(prim, args) {
    const adapter = typeof inmem.getAdapter === 'function' ? inmem.getAdapter(prim) : inmem[prim];
    if (typeof adapter !== 'function') {
      throw new Error(`missing adapter for ${prim}`);
    }
    const primId = typeof inmem.canonicalPrim === 'function' ? inmem.canonicalPrim(prim) : prim;
    const effect = typeof inmem.effectFor === 'function' ? inmem.effectFor(prim) : '';
    const ts = nextTimestampMs();
    events.push({ ts, prim_id: primId, args, region: '', effect: effect ?? '' });
    recordEffect(effects, effect);
    const state = typeof inmem.state === 'object' ? inmem.state : undefined;
    await adapter(args, state);
  }

  await invoke('emit-metric', { name: 'pilot.replay.start' });
  await invoke('publish', {
    topic: 'orders',
    key: 'o-1',
    payload: '{"sym":"ABC","side":"buy","qty":1}',
  });
  await invoke('emit-metric', { name: 'pilot.exec.sent' });
  await invoke('write-object', {
    uri: 'res://ledger/pilot',
    key: 'o-1',
    value: 'filled',
  });
  await invoke('emit-metric', { name: 'pilot.ledger.write' });

  return { effects, events };
}

const { effects, events } = await runManual();

const traceLines = events.map((event) => JSON.stringify(event)).join('\n') + '\n';
writeFileSync(tracePath, traceLines);

const status = {
  ok: true,
  ops: events.length,
  effects: Array.from(effects).sort(),
  manifest_path: manifestPath,
};
writeFileSync(statusPath, `${JSON.stringify(status, null, 2)}\n`);

const summaryProc = spawnSync('node', [traceSummaryBinary], { input: traceLines, encoding: 'utf8' });
if (summaryProc.status !== 0) {
  process.exit(summaryProc.status ?? 1);
}
const summaryJson = JSON.parse(summaryProc.stdout);
writeFileSync(summaryPath, `${JSON.stringify(summaryJson)}\n`);

console.log('pilot handwritten runner complete');
