import { execSync, spawnSync } from 'node:child_process';
import { openDb, count, list, getClaim } from '../src/db.js';
import { queryHash } from '../src/util.js';
import type { Filters } from '../src/types.js';
import { it, expect } from 'vitest';

it('has no binary DB files tracked', () => {
  const out = execSync("git ls-files '*.db' '*.sqlite*'").toString().trim();
  expect(out).toBe('');
});

it('imports only sql.js and uses .js internal imports', () => {
  const sqljs = execSync("rg \"from 'sql.js'\" -n src").toString();
  expect(sqljs.length).toBeGreaterThan(0);
  const sqlite3 = spawnSync('rg', ['sqlite3', 'src']);
  expect(sqlite3.status).not.toBe(0);
  const imports = execSync("rg \"from './\" src").toString().trim().split('\n');
  for (const l of imports) if (l) expect(l).toMatch(/\.js'/);
});

it('guards against SQL injection', () => {
  const db = openDb();
  const inj = "' OR 1=1 --";
  const safe = count(db, { jurisdiction: 'NOWHERE' });
  const injected = count(db, { jurisdiction: inj });
  expect(injected.n).toBe(safe.n);
});

it('count is deterministic with ≥10 evidence samples', () => {
  const db = openDb();
  const filters: Filters = {};
  const results = Array.from({ length: 3 }, () => JSON.stringify(count(db, filters)));
  expect(results[1]).toBe(results[0]);
  expect(results[2]).toBe(results[0]);
  const parsed = JSON.parse(results[0]);
  expect(parsed.dataset_version).toBe('ro-mini-2025-09-09');
  expect(parsed.query_hash).toBe(queryHash(filters));
  const hashes = new Set(
    parsed.samples.map((s: Record<string, unknown>) => String((s as { hash: string }).hash)),
  );
  expect(hashes.size).toBeGreaterThanOrEqual(10);
});

it('list uses SQL paging with LIMIT/OFFSET and is stable', () => {
  const srcLimit = execSync("rg 'LIMIT \\? OFFSET \\?' src/db.ts").toString();
  expect(srcLimit.length).toBeGreaterThan(0);
  const slice = spawnSync('rg', ['slice', 'src/db.ts']);
  expect(slice.status).not.toBe(0);
  const db = openDb();
  const filters: Filters = { limit: 5, offset: 2 };
  const r1 = JSON.stringify(list(db, filters));
  const r2 = JSON.stringify(list(db, filters));
  const r3 = JSON.stringify(list(db, filters));
  expect(r2).toBe(r1);
  expect(r3).toBe(r1);
});

it('getClaim fetches a clause with evidence', () => {
  const db = openDb();
  const claim = getClaim(db, 'C1');
  expect(claim).not.toBeNull();
  expect(claim!.evidence.length).toBeGreaterThan(0);
});
