import { execSync, spawnSync } from 'node:child_process';
import { openDb, count, list } from '../src/db.js';
import { queryHash } from '../src/util.js';
import { buildServer } from '../src/server.js';
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

it('paging via SQL LIMIT/OFFSET yields stable slices', () => {
  const scan = execSync("rg 'LIMIT' src/db.ts").toString();
  expect(scan.length).toBeGreaterThan(0);
  const slice = spawnSync('rg', ['slice', 'src/db.ts']);
  expect(slice.status).not.toBe(0);
  const db = openDb();
  const filters: Filters = { limit: 5, offset: 5 };
  const r1 = JSON.stringify(list(db, filters));
  const r2 = JSON.stringify(list(db, filters));
  const r3 = JSON.stringify(list(db, filters));
  expect(r1).toBe(r2);
  expect(r1).toBe(r3);
});

it('count returns deterministic results with ≥10 distinct evidence', () => {
  const db = openDb();
  const filters: Filters = {};
  const runs = Array.from({ length: 3 }, () => JSON.stringify(count(db, filters)));
  expect(runs[0]).toBe(runs[1]);
  expect(runs[0]).toBe(runs[2]);
  const parsed = JSON.parse(runs[0]);
  expect(parsed.dataset_version).toBe('ro-mini-2025-09-09');
  expect(parsed.query_hash).toBe(queryHash(filters as Record<string, unknown>));
  expect(new Set(parsed.samples.map((s: { hash: string }) => s.hash)).size).toBeGreaterThanOrEqual(10);
});

it('core endpoints deterministic and injection-safe', async () => {
  const app = buildServer();
  const c1 = await app.inject({ url: '/claims/count' });
  const c2 = await app.inject({ url: '/claims/count' });
  const c3 = await app.inject({ url: '/claims/count' });
  expect(c1.payload).toBe(c2.payload);
  expect(c1.payload).toBe(c3.payload);
  const l1 = await app.inject({ url: '/claims/list?limit=5' });
  const l2 = await app.inject({ url: '/claims/list?limit=5' });
  const l3 = await app.inject({ url: '/claims/list?limit=5' });
  expect(l1.payload).toBe(l2.payload);
  expect(l1.payload).toBe(l3.payload);
  const inj = await app.inject({
    url: '/claims/list?jurisdiction=' + encodeURIComponent("' OR 1=1 --"),
  });
  const safe = await app.inject({ url: '/claims/list?jurisdiction=fake' });
  expect(inj.statusCode).toBe(200);
  expect(safe.statusCode).toBe(200);
  expect(inj.json().total).toBe(0);
  expect(safe.json().total).toBe(0);
  await app.close();
});

it('invalid limit returns 400', async () => {
  const app = buildServer();
  const res = await app.inject({ url: '/claims/list?limit=foo' });
  expect(res.statusCode).toBe(400);
  await app.close();
});

