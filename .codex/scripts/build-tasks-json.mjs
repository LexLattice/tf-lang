#!/usr/bin/env node
import fs from 'node:fs/promises';
import path from 'node:path';

const ROOT = path.resolve('.codex/tasks');
const OUT = path.resolve('.codex/tasks.json');

const want = ['END_GOAL.md', 'BLOCKERS.yml', 'ACCEPTANCE.md'];

const readFileSafe = async (p) => {
  try { return await fs.readFile(p, 'utf8'); } catch { return null; }
};

const main = async () => {
  const dirs = (await fs.readdir(ROOT, { withFileTypes: true }))
    .filter(d => d.isDirectory())
    .map(d => d.name)
    .sort((a,b)=>a.localeCompare(b));

  const out = {};
  for (const d of dirs) {
    const base = path.join(ROOT, d);
    const files = new Set(await fs.readdir(base));
    // Only include if at least one of the expected files exists
    if (![...want].some(f => files.has(f))) continue;
    const entry = {};
    // Read in stable order
    for (const f of want) {
      const p = path.join(base, f);
      entry[f.replace(/\..*$/, '')] = await readFileSafe(p);
    }
    out[d] = entry;
  }

  // Canonical stringify: sort keys recursively
  const canon = (v) => {
    if (v === null) return null;
    if (Array.isArray(v)) return v.map(canon);
    if (v instanceof Map) {
      // Tagged encoding keeps Map identity while ensuring deterministic ordering.
      const entries = Array.from(v.entries()).map(([key, value]) => [canon(key), canon(value)]);
      entries.sort((a, b) => JSON.stringify(a[0]).localeCompare(JSON.stringify(b[0])));
      return { __kind: 'Map', entries };
    }
    if (v instanceof Set) {
      // Tagged encoding keeps Set identity with deterministic member order.
      const values = Array.from(v.values()).map(item => canon(item));
      values.sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b)));
      return { __kind: 'Set', values };
    }
    if (typeof v === 'object') {
      const k = Object.keys(v).sort();
      const o = {};
      for (const key of k) {
        o[key] = canon(v[key]);
      }
      return o;
    }
    return v;
  };
  const json = JSON.stringify(canon(out), null, 2) + '\n';
  await fs.writeFile(OUT, json);
  console.log(`[tasks-json] wrote ${OUT}`);
};

main().catch(err => { console.error(err); process.exit(1); });
