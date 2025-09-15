#!/usr/bin/env node
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

// Simple canonical JSON stringify: sort object keys recursively
const canon = (v) => {
  if (Array.isArray(v)) return v.map(canon);
  if (v && typeof v === 'object') {
    const out = {};
    for (const k of Object.keys(v).sort()) out[k] = canon(v[k]);
    return out;
  }
  return v;
};
const canonStringify = (v) => JSON.stringify(canon(v));

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const pkgRoot = path.resolve(__dirname, '../../packages/oracles-core-ts');
// Prefer built dist first (reproducibility), then fall back to TS sources
const mod = await import(path.join(pkgRoot, 'dist/src/index.js')).catch(async () => {
  return import(path.join(pkgRoot, 'src/index.ts'));
});

const samples = {
  equals: {
    ok: mod.equals({ a: 1 }, { a: 1 }),
    fail: mod.equals({ a: 1 }, { a: 2 })
  },
  subsetOf: {
    ok: mod.subsetOf({ a: 1 }, { a: 1, b: 2 }),
    fail: mod.subsetOf({ a: 1, x: 1 }, { a: 1, b: 2 })
  },
  inRange: {
    ok: mod.inRange(5, 1, 10),
    fail: mod.inRange(0, 1, 10)
  },
  matchesRegex: {
    ok: mod.matchesRegex('abc123', /^[a-z]+\d+$/),
    fail: mod.matchesRegex('abc', /^\d+$/)
  },
  nonEmpty: {
    ok: mod.nonEmpty([1]),
    fail: mod.nonEmpty('')
  }
};

await fs.mkdir('oracle-core', { recursive: true });
const json = canonStringify({ results: samples });
await fs.writeFile('oracle-core/results.json', json + '\n');

const lines = ['# Oracle Core Results'];
const names = Object.keys(samples).sort();
let okCount = 0;
let failCount = 0;
const codeTallies = new Map();
for (const name of names) {
  const pair = samples[name];
  lines.push(`\n## ${name}`);
  lines.push('- ok: ' + JSON.stringify(pair.ok));
  lines.push('- fail: ' + JSON.stringify(pair.fail));
  if (pair.ok?.ok === true) {
    okCount++;
  } else {
    failCount++;
  }
  if (pair.fail && pair.fail.code) {
    const c = String(pair.fail.code);
    codeTallies.set(c, (codeTallies.get(c) || 0) + 1);
  }
}
const codeSummary = Array.from(codeTallies.entries())
  .sort((a,b) => a[0].localeCompare(b[0]))
  .map(([c,n]) => `${c}=${n}`).join(' ');
lines.push(`\nTOTAL: ${names.length} oracles, ${okCount} OK, ${failCount} FAIL${codeSummary ? ` (codes: ${codeSummary})` : ''}`);
await fs.writeFile('oracle-core/results.md', lines.join('\n') + '\n');
console.log('Wrote oracle-core/results.(json|md)');
