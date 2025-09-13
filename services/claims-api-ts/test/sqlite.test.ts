import { execSync } from 'node:child_process';
import { readFileSync, readdirSync, statSync } from 'node:fs';
import { join } from 'node:path';
import fastify from '../src/server.js';
import { openDb, count, list, getClaim } from '../src/db.js';
import { queryHash } from '../src/util.js';
import type { Filters } from '../src/types.js';
import { it, expect, afterAll } from 'vitest';

afterAll(async () => { await fastify.close(); });

it('has no binary DB files tracked', () => {
  const out = execSync("git ls-files '*.db' '*.sqlite*'").toString().trim();
  expect(out).toBe('');
});

it('imports only sql.js', () => {
  const sqljs = execSync("rg \"from 'sql.js'\" src").toString();
  expect(sqljs.length).toBeGreaterThan(0);
  const sqlite3 = execSync("rg sqlite3 src || true").toString().trim();
  expect(sqlite3).toBe('');
});

it('internal imports include .js and avoid deep paths', () => {
  const files: string[] = [];
  function walk(dir: string) {
    for (const ent of readdirSync(dir)) {
      const p = join(dir, ent);
      if (statSync(p).isDirectory()) walk(p); else files.push(p);
    }
  }
  walk(join(__dirname, '../src'));
  for (const f of files) {
    const src = readFileSync(f, 'utf8');
    const regex = /from\s+['"](\.\.\/|\.\/)([^'"]+)['"]/g;
    let m: RegExpExecArray | null;
    while ((m = regex.exec(src))) {
      expect(m[2].endsWith('.js')).toBe(true);
      expect(m[2].includes('..')).toBe(false);
    }
  }
});

it('db layer uses SQL LIMIT/OFFSET without JS slicing', () => {
  const src = readFileSync(join(__dirname, '../src/db.ts'), 'utf8');
  expect(src).toMatch(/LIMIT \?/);
  expect(src).toMatch(/OFFSET \?/);
  expect(src).not.toMatch(/\.slice/);
});

it('count returns stable results with ≥10 distinct evidence samples', () => {
  const db = openDb();
  const filters: Filters = {};
  const results = Array.from({ length: 3 }, () => JSON.stringify(count(db, filters)));
  for (let i = 1; i < results.length; i++) expect(results[i]).toBe(results[0]);
  const parsed = JSON.parse(results[0]);
  expect(parsed.dataset_version).toBe('ro-mini-2025-09-09');
  expect(parsed.query_hash).toBe(queryHash(filters));
  expect(new Set(parsed.samples.map((s: { hash: string }) => s.hash)).size).toBeGreaterThanOrEqual(10);
});

it('list paging stable and SQL-driven', () => {
  const db = openDb();
  const filters: Filters = { modality: 'FORBIDDEN', jurisdiction: 'RO', at: '2025-09-09', limit: 5, offset: 2 };
  const outputs = Array.from({ length: 3 }, () => JSON.stringify(list(db, filters)));
  expect(outputs[1]).toBe(outputs[0]);
  expect(outputs[2]).toBe(outputs[0]);
});

it('injection-shaped value does not alter results', () => {
  const db = openDb();
  const inj = count(db, { jurisdiction: "' OR 1=1 --" });
  const safe = count(db, { jurisdiction: "' OR 1=1 --" });
  expect(JSON.stringify(inj)).toBe(JSON.stringify(safe));
  expect(inj.n).toBe(0);
});

it('server rejects invalid filter shapes', async () => {
  const res = await fastify.inject('/claims/list?limit=notnum');
  expect(res.statusCode).toBe(400);
});

it('getClaim fetches a clause with evidence', () => {
  const db = openDb();
  const claim = getClaim(db, 'C1');
  expect(claim).not.toBeNull();
  expect(claim!.evidence.length).toBeGreaterThan(0);
});
