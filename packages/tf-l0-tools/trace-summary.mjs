#!/usr/bin/env node
import { parseArgs } from 'node:util';

function parseOptions() {
  const { values } = parseArgs({
    options: {
      top: { type: 'string' },
      pretty: { type: 'boolean', default: false },
      quiet: { type: 'boolean', default: false }
    }
  });
  let top = Number.POSITIVE_INFINITY;
  if (typeof values.top === 'string' && values.top.length > 0) {
    const parsed = Number.parseInt(values.top, 10);
    if (!Number.isNaN(parsed) && parsed > 0) {
      top = parsed;
    } else if (parsed === 0) {
      top = 0;
    }
  }
  return { top, pretty: Boolean(values.pretty), quiet: Boolean(values.quiet) };
}

function sortEntries(map) {
  return Array.from(map.entries()).sort((a, b) => {
    if (b[1] !== a[1]) return b[1] - a[1];
    return a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0;
  });
}

function accumulate(summary, entry) {
  if (!entry || typeof entry !== 'object') {
    return;
  }
  summary.total += 1;
  if (typeof entry.prim_id === 'string') {
    summary.byPrim.set(entry.prim_id, (summary.byPrim.get(entry.prim_id) || 0) + 1);
  }
  if (typeof entry.effect === 'string') {
    summary.byEffect.set(entry.effect, (summary.byEffect.get(entry.effect) || 0) + 1);
  }
}

async function readLines() {
  const chunks = [];
  for await (const chunk of process.stdin) {
    chunks.push(typeof chunk === 'string' ? chunk : chunk.toString('utf8'));
  }
  return chunks.join('');
}

function selectTop(entries, limit) {
  if (!Number.isFinite(limit)) {
    return entries;
  }
  if (limit <= 0) {
    return [];
  }
  return entries.slice(0, limit);
}

function entriesToObject(entries) {
  const out = {};
  for (const [key, value] of entries) {
    out[key] = value;
  }
  return out;
}

async function main() {
  const options = parseOptions();
  const buffer = await readLines();
  const summary = { total: 0, byPrim: new Map(), byEffect: new Map() };
  let warned = false;
  for (const line of buffer.split(/\r?\n/)) {
    const trimmed = line.trim();
    if (!trimmed) continue;
    try {
      const parsed = JSON.parse(trimmed);
      accumulate(summary, parsed);
    } catch (err) {
      if (!options.quiet && !warned) {
        console.warn('trace-summary: ignoring malformed line');
        warned = true;
      }
    }
  }

  const primEntries = sortEntries(summary.byPrim);
  const effectEntries = sortEntries(summary.byEffect);
  const limitedPrim = selectTop(primEntries, options.top);
  const limitedEffect = selectTop(effectEntries, options.top);

  const payload = {
    total: summary.total,
    by_prim: entriesToObject(limitedPrim),
    by_effect: entriesToObject(limitedEffect)
  };

  const json = options.pretty ? JSON.stringify(payload, null, 2) : JSON.stringify(payload);
  process.stdout.write(json);
  process.stdout.write('\n');
}

await main();
