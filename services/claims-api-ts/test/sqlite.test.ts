import { execSync, spawnSync } from 'node:child_process';
import { readdirSync, readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { openDb, count, list } from '../src/db.js';
import { queryHash } from '../src/util.js';
import { buildApp } from '../src/app.js';
import type { Filters } from '../src/types.js';
import { describe, it, expect } from 'vitest';

const __dirname = dirname(fileURLToPath(import.meta.url));

it('has no binary DB files tracked', () => {
  const out = execSync("git ls-files '*.db' '*.sqlite*'").toString().trim();
  expect(out).toBe('');
});

it('imports only sql.js', () => {
  const root = join(__dirname, '../../..');
  const sqljs = execSync(`rg "from 'sql.js'" ${root}`).toString();
  expect(sqljs.length).toBeGreaterThan(0);
  const sqlite3 = spawnSync('rg', ['sqlite3', '--glob', 'src/**', '--glob', 'package.json', root]);
  expect(sqlite3.status).not.toBe(0);
  const better = spawnSync('rg', ['better-sqlite3', '--glob', 'src/**', '--glob', 'package.json', root]);
  expect(better.status).not.toBe(0);
});

describe('deterministic queries with parameterization', () => {
  const db = openDb();

  it('returns stable counts and distinct evidence', () => {
    const filters: Filters = {};
    const results = Array.from({ length: 3 }, () => JSON.stringify(count(db, filters)));
    expect(results[1]).toBe(results[0]);
    expect(results[2]).toBe(results[0]);
    const parsed = JSON.parse(results[0]);
    expect(parsed.dataset_version).toBe('ro-mini-2025-09-09');
    expect(parsed.query_hash).toBe(queryHash(filters));
    expect(new Set(parsed.samples.map((s: { hash: string }) => s.hash)).size).toBeGreaterThanOrEqual(10);
  });

  it('prepared vs exec produce identical JSON', () => {
    const filters: Filters = {};
    const prepared = JSON.stringify(count(db, filters));
    const n = db.db.exec('SELECT COUNT(*) as c FROM claims;')[0].values[0][0] as number;
    const ev = db.db.exec(
      "SELECT DISTINCT json_extract(data,'$.evidence[0]') as ev FROM claims ORDER BY id LIMIT 10;"
    )[0].values.map(v => JSON.parse(v[0] as string));
    const direct = JSON.stringify({
      dataset_version: db.datasetVersion,
      query_hash: queryHash(filters),
      filters,
      n,
      samples: ev,
    });
    expect(direct).toBe(prepared);
  });

  it('applies paging via SQL LIMIT/OFFSET', () => {
    const filters: Filters = { modality: 'FORBIDDEN', jurisdiction: 'RO', at: '2024-01-01', limit: 5, offset: 5 };
    const runs = Array.from({ length: 3 }, () => JSON.stringify(list(db, filters)));
    expect(runs[1]).toBe(runs[0]);
    expect(runs[2]).toBe(runs[0]);
    const parsed = JSON.parse(runs[0]);
    expect(parsed.items.length).toBe(5);
    expect(parsed.items[0].id).toBe('A13');
    const grep = execSync("rg 'LIMIT \\? OFFSET \\?' src/db.ts").toString().trim();
    expect(grep.length).toBeGreaterThan(0);
    const noSlice = spawnSync('rg', ['\\.slice\\(', 'src']);
    expect(noSlice.status).not.toBe(0);
    const noFilter = spawnSync('rg', ['\\.filter\\(', 'src']);
    expect(noFilter.status).not.toBe(0);
  });

  it('handles large offset deterministically', () => {
    const filters: Filters = { limit: 5, offset: 9999 };
    const runs = Array.from({ length: 3 }, () => JSON.stringify(list(db, filters)));
    expect(runs[1]).toBe(runs[0]);
    expect(runs[2]).toBe(runs[0]);
    const parsed = JSON.parse(runs[0]);
    expect(parsed.items.length).toBe(0);
  });
});

it('400 on invalid filter shapes', async () => {
  const app = buildApp();
  const r1 = await app.inject({ method: 'GET', url: '/claims/list?limit=-1' });
  expect(r1.statusCode).toBe(400);
  const r2 = await app.inject({ method: 'GET', url: '/claims/list?limit=0' });
  expect(r2.statusCode).toBe(400);
  const r3 = await app.inject({ method: 'GET', url: '/claims/list?offset=-5' });
  expect(r3.statusCode).toBe(400);
});

it('hygiene: .js internal imports and no deep imports', () => {
  const srcDir = join(__dirname, '../src');
  for (const file of readdirSync(srcDir)) {
    if (!file.endsWith('.ts')) continue;
    const text = readFileSync(join(srcDir, file), 'utf8');
    const lines = text.split('\n').filter(l => l.startsWith('import'));
    for (const line of lines) {
      if (line.includes("'./") || line.includes('"./')) {
        expect(line.includes('.js')).toBe(true);
      }
      expect(/@tf-lang\/[^']+\//.test(line)).toBe(false);
    }
  }
});

it('injection value behaves like ordinary string', () => {
  const db = openDb();
  const inj = "' OR 1=1 --";
  const r1 = count(db, { jurisdiction: inj });
  const r2 = count(db, { jurisdiction: 'NONEXIST' });
  expect(r1.n).toBe(r2.n);
});
