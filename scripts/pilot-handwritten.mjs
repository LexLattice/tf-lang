#!/usr/bin/env node
import { mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { join, dirname, isAbsolute } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import inmem from '../packages/tf-l0-codegen-ts/src/runtime/inmem.mjs';
import { canonicalize, canonicalStringify } from './hash-jsonl.mjs';
import { resetDeterministicClock } from './pilot-clock.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, '..');
const workdir = process.env.TF_PILOT_WORKDIR;
const outRoot = workdir
  ? (isAbsolute(workdir) ? workdir : join(root, workdir))
  : join(root, 'out', '0.4');
const pilotDir = join(outRoot, 'pilot-l0');
const manualDir = join(pilotDir, 'manual');
const traceSummaryCli = join(root, 'packages', 'tf-l0-tools', 'trace-summary.mjs');

mkdirSync(manualDir, { recursive: true });

const statusPath = join(manualDir, 'status.json');
const tracePath = join(manualDir, 'trace.jsonl');
const summaryPath = join(manualDir, 'summary.json');

for (const path of [statusPath, tracePath, summaryPath]) {
  rmSync(path, { force: true });
}

process.env.TF_STATUS_PATH = statusPath;
process.env.TF_TRACE_PATH = tracePath;

resetDeterministicClock();
if (typeof inmem.reset === 'function') {
  inmem.reset();
}

const clock = globalThis.__tf_clock;
if (!clock || typeof clock.nowNs !== 'function') {
  console.error('pilot-handwritten: deterministic clock missing');
  process.exit(1);
}

const records = [];
let ops = 0;
const effects = new Set();

function nextTs() {
  return Number(clock.nowNs() / 1_000_000n);
}

async function invoke(prim, args) {
  const adapter = typeof inmem.getAdapter === 'function' ? inmem.getAdapter(prim) : inmem[prim];
  if (typeof adapter !== 'function') {
    throw new Error(`No adapter for primitive ${prim}`);
  }
  const ts = nextTs();
  const primId = typeof inmem.canonicalPrim === 'function' ? inmem.canonicalPrim(prim) : prim;
  const effect = typeof inmem.effectFor === 'function' ? inmem.effectFor(prim) : '';
  if (effect) {
    effects.add(effect);
  }
  const traceArgs = canonicalize(args ?? {});
  records.push({ ts, prim_id: primId, args: traceArgs, region: '', effect: effect || '' });
  ops += 1;
  return adapter(args, inmem.state ?? {});
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

const traceLines = records.map((record) => JSON.stringify(record));
writeFileSync(tracePath, traceLines.join('\n') + '\n', 'utf8');

const status = {
  ok: true,
  ops,
  effects: Array.from(effects).sort(),
};
writeFileSync(statusPath, JSON.stringify(status, null, 2) + '\n', 'utf8');

const summaryProc = spawnSync('node', [traceSummaryCli], {
  input: traceLines.join('\n') + '\n',
  encoding: 'utf8',
});
if (summaryProc.status !== 0) {
  process.exit(summaryProc.status ?? 1);
}
const summaryJson = JSON.parse(summaryProc.stdout);
writeFileSync(summaryPath, canonicalStringify(summaryJson) + '\n', 'utf8');

console.log('pilot-handwritten complete');
