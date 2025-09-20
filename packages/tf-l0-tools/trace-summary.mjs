#!/usr/bin/env node
import { parseArgs } from 'node:util';

const {
  values: { top, pretty = false, quiet = false },
  positionals,
} = parseArgs({
  options: {
    top: { type: 'string' },
    pretty: { type: 'boolean', default: false },
    quiet: { type: 'boolean', default: false },
  },
  allowPositionals: true,
});

if (positionals.length > 0) {
  console.error('trace-summary: unexpected positional arguments:', positionals.join(' '));
  process.exit(1);
}

let limit = null;
if (top !== undefined) {
  const parsed = Number.parseInt(top, 10);
  if (Number.isNaN(parsed) || parsed <= 0) {
    console.error('trace-summary: --top must be a positive integer');
    process.exit(1);
  }
  limit = parsed;
}

const decoder = new TextDecoder();
const chunks = [];
for await (const chunk of process.stdin) {
  chunks.push(typeof chunk === 'string' ? chunk : decoder.decode(chunk));
}

const input = chunks.join('');
const lines = input.split(/\r?\n/);

let warned = false;
let total = 0;
const byPrim = new Map();
const byEffect = new Map();

for (const line of lines) {
  const trimmed = line.trim();
  if (!trimmed) continue;
  let record;
  try {
    record = JSON.parse(trimmed);
  } catch (error) {
    if (!quiet && !warned) {
      console.warn('trace-summary: ignoring malformed JSON line');
      warned = true;
    }
    continue;
  }

  total += 1;
  const primId = typeof record?.prim_id === 'string' && record.prim_id ? record.prim_id : 'unknown';
  byPrim.set(primId, (byPrim.get(primId) ?? 0) + 1);

  const effects = collectEffects(record);
  if (effects.length === 0) {
    byEffect.set('unknown', (byEffect.get('unknown') ?? 0) + 1);
  } else {
    for (const effect of effects) {
      byEffect.set(effect, (byEffect.get(effect) ?? 0) + 1);
    }
  }
}

const summary = {
  total,
  by_prim: toObject(byPrim, limit),
  by_effect: toObject(byEffect, limit),
};

const json = JSON.stringify(summary, null, pretty ? 2 : 0);
process.stdout.write(json + '\n');

function collectEffects(record) {
  const effects = [];
  if (typeof record?.effect === 'string' && record.effect) {
    effects.push(record.effect);
  }
  if (Array.isArray(record?.effects)) {
    for (const entry of record.effects) {
      if (typeof entry === 'string' && entry) {
        effects.push(entry);
      }
    }
  }
  return effects;
}

function toObject(map, topLimit) {
  const entries = Array.from(map.entries()).sort((a, b) => {
    if (b[1] !== a[1]) {
      return b[1] - a[1];
    }
    return a[0].localeCompare(b[0]);
  });
  const sliced = topLimit ? entries.slice(0, topLimit) : entries;
  const out = {};
  for (const [key, value] of sliced) {
    out[key] = value;
  }
  return out;
}
