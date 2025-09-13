import { execSync, spawnSync } from 'node:child_process';
import { readdirSync, readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { openDb, count, list } from '../src/db.js';
import { queryHash } from '../src/util.js';
import { buildApp } from '../src/app.js';
import { buildDb } from '@tf-lang/d1-sqlite';
import type { Filters, Evidence, CountResult } from '../src/types.js';
import { describe, it, expect } from 'vitest';

it('has no binary DB files tracked', () => {
  const out = execSync("git ls-files '*.db' '*.sqlite*'").toString().trim();
  expect(out).toBe('');
});

it('imports only sql.js', () => {
  const sqljs = execSync("rg \"from 'sql.js'\" src").toString();
  expect(sqljs.length).toBeGreaterThan(0);
  const sqlite3 = spawnSync('rg', ['sqlite3', 'src']);
  expect(sqlite3.status).not.toBe(0);
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

  it('applies paging via SQL LIMIT/OFFSET', () => {
    const filters: Filters = { modality: 'FORBIDDEN', jurisdiction: 'RO', at: '2024-01-01', limit: 5, offset: 5 };
    const runs = Array.from({ length: 3 }, () => JSON.stringify(list(db, filters)));
    expect(runs[1]).toBe(runs[0]);
    expect(runs[2]).toBe(runs[0]);
    const parsed = JSON.parse(runs[0]);
    expect(parsed.items.length).toBe(5);
    expect(parsed.items[0].id).toBe('A13');
    const grep = execSync("rg 'LIMIT \\?4 OFFSET \\?5' src/db.ts").toString().trim();
    expect(grep.length).toBeGreaterThan(0);
    const noSlice = spawnSync('rg', ['slice', 'src']);
    expect(noSlice.status).not.toBe(0);
    const noFilter = spawnSync('rg', ['\\.filter\\(', 'src']);
    expect(noFilter.status).not.toBe(0);
  });

  it('large offset yields empty page deterministically', () => {
    const filters: Filters = { limit: 5, offset: 999 };
    const runs = Array.from({ length: 3 }, () => JSON.stringify(list(db, filters)));
    expect(runs[1]).toBe(runs[0]);
    expect(runs[2]).toBe(runs[0]);
    const parsed = JSON.parse(runs[0]);
    expect(parsed.items.length).toBe(0);
    expect(parsed.total).toBeGreaterThan(0);
  });
});

it('400 on invalid filter shapes deterministically', async () => {
  const app = buildApp();
  const qs = ['/claims/list?limit=-1', '/claims/list?limit=0', '/claims/list?offset=-1'];
  for (const q of qs) {
    const bodies: string[] = [];
    for (let i = 0; i < 3; i++) {
      const res = await app.inject({ method: 'GET', url: q });
      expect(res.statusCode).toBe(400);
      bodies.push(res.body);
    }
    expect(bodies[1]).toBe(bodies[0]);
    expect(bodies[2]).toBe(bodies[0]);
  }
});

it('hygiene: .js internal imports and no deep imports', () => {
  const __dirname = dirname(fileURLToPath(import.meta.url));
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

function directCount(f: Filters): CountResult {
  const db = buildDb();
  const res = db.exec("SELECT value FROM meta WHERE key='dataset_version';");
  const datasetVersion = res[0]?.values?.[0]?.[0];
  const where = [
    'WHERE (?1 IS NULL OR modality = ?1)',
    '(?2 IS NULL OR jurisdiction = ?2)',
    "(?3 IS NULL OR (effective_from <= ?3 AND (?3 <= IFNULL(effective_to, '9999-12-31'))))",
  ].join(' AND ');
  const params = [f.modality ?? null, f.jurisdiction ?? null, f.at ?? null];
  const stmt = db.prepare(`SELECT COUNT(*) as c FROM claims ${where};`);
  stmt.bind(params);
  stmt.step();
  const row = stmt.getAsObject();
  const n = typeof row.c === 'number' ? row.c : 0;
  stmt.reset();
  const evStmt = db.prepare(
    `SELECT DISTINCT json_extract(data,'$.evidence[0]') as ev FROM claims ${where} ORDER BY id LIMIT 10;`
  );
  evStmt.bind(params);
  const samples: Evidence[] = [];
  while (evStmt.step()) {
    const r = evStmt.getAsObject();
    if (typeof r.ev === 'string') samples.push(JSON.parse(r.ev) as Evidence);
  }
  evStmt.reset();
  return {
    dataset_version: typeof datasetVersion === 'string' ? datasetVersion : '',
    query_hash: queryHash(f),
    filters: f,
    n,
    samples,
  };
}

it('prepared vs direct execution match byte-for-byte', () => {
  const db = openDb();
  const filters: Filters = { modality: 'FORBIDDEN' };
  const prepared = JSON.stringify(count(db, filters));
  const direct = JSON.stringify(directCount(filters));
  expect(prepared).toBe(direct);
});
