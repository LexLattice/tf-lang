#!/usr/bin/env node
import { parseArgs } from 'node:util';
import { createInterface } from 'node:readline';

const {
  values: { top: rawTop, pretty = false, quiet = false, help = false },
  positionals,
} = parseArgs({
  options: {
    top: { type: 'string' },
    pretty: { type: 'boolean', default: false },
    quiet: { type: 'boolean', default: false },
    help: { type: 'boolean', default: false },
  },
  allowPositionals: true,
});

if (positionals.length > 0) {
  console.error('trace-summary: unexpected positional arguments:', positionals.join(' '));
  process.exit(1);
}

if (help) {
  console.log('Usage: trace-summary [--top=N] [--pretty] [--quiet]');
  console.log('Reads trace JSONL from stdin and prints aggregate counts.');
  process.exit(0);
}

const top = rawTop === undefined ? Infinity : Number.parseInt(rawTop, 10);
if (!Number.isFinite(top) || top < 0) {
  console.error('trace-summary: --top must be a non-negative integer');
  process.exit(1);
}

const byPrim = new Map();
const byEffect = new Map();
let total = 0;
let warned = false;

const rl = createInterface({
  input: process.stdin,
  crlfDelay: Infinity,
});

rl.on('line', (line) => {
  const trimmed = line.trim();
  if (trimmed.length === 0) {
    return;
  }
  try {
    const record = JSON.parse(trimmed);
    total += 1;
    const prim = typeof record.prim_id === 'string' ? record.prim_id : null;
    const effect = typeof record.effect === 'string' ? record.effect : null;
    if (prim) increment(byPrim, prim);
    if (effect) increment(byEffect, effect);
  } catch (error) {
    if (!quiet && !warned) {
      console.error('trace-summary: skipping malformed line');
      warned = true;
    }
  }
});

rl.on('close', () => {
  const summary = {
    total,
    by_prim: pickTop(byPrim, top),
    by_effect: pickTop(byEffect, top),
  };
  const payload = pretty ? JSON.stringify(summary, null, 2) : JSON.stringify(summary);
  process.stdout.write(payload);
  if (pretty) {
    process.stdout.write('\n');
  }
});

function increment(map, key) {
  const current = map.get(key) ?? 0;
  map.set(key, current + 1);
}

function pickTop(map, limit) {
  const entries = Array.from(map.entries());
  entries.sort((a, b) => {
    if (b[1] !== a[1]) return b[1] - a[1];
    return a[0].localeCompare(b[0]);
  });
  const slice = Number.isFinite(limit) ? entries.slice(0, limit) : entries;
  const result = {};
  for (const [key, value] of slice) {
    result[key] = value;
  }
  return result;
}
