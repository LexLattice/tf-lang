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
const mod = await import(path.join(pkgRoot, 'src/index.ts')).catch(async () => {
  // fallback to dist after build
  return import(path.join(pkgRoot, 'dist/src/index.js'));
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
for (const [name, pair] of Object.entries(samples).sort()) {
  lines.push(`\n## ${name}`);
  lines.push('- ok: ' + JSON.stringify(pair.ok));
  lines.push('- fail: ' + JSON.stringify(pair.fail));
}
await fs.writeFile('oracle-core/results.md', lines.join('\n') + '\n');
console.log('Wrote oracle-core/results.(json|md)');

