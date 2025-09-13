import { execSync, spawnSync } from 'node:child_process';
import { openDb, count, list, getClaim } from '../src/db.js';
import { queryHash } from '../src/util.js';
import type { Filters } from '../src/types.js';
import { it, expect } from 'vitest';

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

it('uses in-memory sql.js and returns stable counts and evidence', () => {
  const db = openDb();
  const filters: Filters = {};
  const results = Array.from({ length: 5 }, () => JSON.stringify(count(db, filters)));
  for (let i = 1; i < results.length; i++) expect(results[i]).toBe(results[0]);
  const parsed = JSON.parse(results[0]);
  expect(parsed.dataset_version).toBe('ro-mini-2025-09-09');
  expect(parsed.query_hash).toBe(queryHash(filters));
  expect(new Set(parsed.samples.map((s: any) => s.hash)).size).toBeGreaterThanOrEqual(10);
});

it('list returns same clauses across runs', () => {
  const db = openDb();
  const filters: Filters = { modality: 'FORBIDDEN', jurisdiction: 'RO', at: '2025-09-09', limit: 5 };
  const r1 = JSON.stringify(list(db, filters));
  const r2 = JSON.stringify(list(db, filters));
  const r3 = JSON.stringify(list(db, filters));
  expect(r1).toBe(r2);
  expect(r1).toBe(r3);
});

it('getClaim fetches a clause with evidence', () => {
  const db = openDb();
  const claim = getClaim(db, 'C1');
  expect(claim).not.toBeNull();
  expect(claim!.evidence.length).toBeGreaterThan(0);
});
