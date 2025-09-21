#!/usr/bin/env node
import { parseArgs } from 'node:util';

function canonicalJson(value) {
  if (Array.isArray(value)) {
    return '[' + value.map(canonicalJson).join(',') + ']';
  }
  if (value && typeof value === 'object') {
    const keys = Object.keys(value).sort();
    return '{' + keys.map((key) => `${JSON.stringify(key)}:${canonicalJson(value[key])}`).join(',') + '}';
  }
  return JSON.stringify(value);
}

function parseTop(value) {
  if (!value) return Infinity;
  const num = Number.parseInt(value, 10);
  if (!Number.isFinite(num) || num <= 0) {
    return Infinity;
  }
  return num;
}

function selectTop(map, limit) {
  const entries = Array.from(map.entries());
  entries.sort((a, b) => {
    if (b[1] !== a[1]) return b[1] - a[1];
    return a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0;
  });
  const sliced = Number.isFinite(limit) ? entries.slice(0, limit) : entries;
  sliced.sort((a, b) => a[0].localeCompare(b[0]));
  const result = {};
  for (const [key, count] of sliced) {
    result[key] = count;
  }
  return result;
}

function increment(map, key) {
  map.set(key, (map.get(key) || 0) + 1);
}

async function readStdin() {
  const chunks = [];
  for await (const chunk of process.stdin) {
    chunks.push(chunk);
  }
  return chunks.join('');
}

const { values } = parseArgs({
  options: {
    top: { type: 'string' },
    pretty: { type: 'boolean' },
    quiet: { type: 'boolean' },
  },
});

const topLimit = parseTop(values.top);
const pretty = Boolean(values.pretty);
const quiet = Boolean(values.quiet);

const input = await readStdin();
const lines = input.split(/\r?\n/);

const primCounts = new Map();
const effectCounts = new Map();
const irHashCounts = new Map();
const manifestHashCounts = new Map();
let total = 0;
let warned = false;

for (const raw of lines) {
  const line = raw.trim();
  if (!line) continue;
  try {
    const parsed = JSON.parse(line);
    total += 1;
    if (parsed && typeof parsed.prim_id === 'string') {
      increment(primCounts, parsed.prim_id);
    }
    if (parsed && typeof parsed.effect === 'string') {
      increment(effectCounts, parsed.effect);
    }
    if (parsed && typeof parsed.meta === 'object' && !Array.isArray(parsed.meta)) {
      if (typeof parsed.meta.ir_hash === 'string') {
        increment(irHashCounts, parsed.meta.ir_hash);
      }
      if (typeof parsed.meta.manifest_hash === 'string') {
        increment(manifestHashCounts, parsed.meta.manifest_hash);
      }
    }
  } catch (err) {
    if (!warned && !quiet) {
      console.warn('trace-summary: skipping malformed line');
      warned = true;
    }
  }
}

const summary = {
  total,
  by_prim: selectTop(primCounts, topLimit),
  by_effect: selectTop(effectCounts, topLimit),
};

if (irHashCounts.size > 0 || manifestHashCounts.size > 0) {
  const byMeta = {};
  if (irHashCounts.size > 0) {
    byMeta.ir_hash = selectTop(irHashCounts, topLimit);
  }
  if (manifestHashCounts.size > 0) {
    byMeta.manifest_hash = selectTop(manifestHashCounts, topLimit);
  }
  summary.by_meta = byMeta;
}

const canonical = canonicalJson(summary);
if (pretty) {
  process.stdout.write(JSON.stringify(JSON.parse(canonical), null, 2) + '\n');
} else {
  process.stdout.write(canonical + '\n');
}
