import { describe, it, expect, beforeAll } from 'vitest';
import initSqlJs from 'sql.js';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { buildServer } from '../src/server.js';
import { queryHash } from '../src/util.js';

let dbPath: string;

beforeAll(async () => {
  dbPath = path.join(os.tmpdir(), `claims-${Date.now()}.db`);
  const SQL = await initSqlJs();
  const db = new SQL.Database();
  db.run(`
    CREATE TABLE meta (key TEXT PRIMARY KEY, value TEXT);
    INSERT INTO meta (key, value) VALUES ('dataset_version', 'd1-test');
    CREATE TABLE claims (
      id TEXT PRIMARY KEY,
      modality TEXT,
      jurisdiction TEXT,
      effective_from TEXT,
      effective_to TEXT,
      text TEXT,
      source_uri TEXT,
      status TEXT
    );
  `);
  const stmt = db.prepare('INSERT INTO claims VALUES (?,?,?,?,?,?,?,?)');
  for (let i = 0; i < 12; i++) {
    stmt.run([String(i + 1), 'FORBIDDEN', 'RO', '2025-01-01', null, `Clause ${i + 1}`, `src${i + 1}`, 'determinate']);
  }
  stmt.free();
  const data = db.export();
  fs.writeFileSync(dbPath, Buffer.from(data));
  db.close();
});

describe('D1: SQLite adapter', () => {
  it('hashes, versions, stability, evidence >=10', async () => {
    const app = await buildServer(dbPath);
    const query = { modality: 'FORBIDDEN', jurisdiction: 'RO', at: '2025-09-09' };
    const expectedHash = queryHash(query);
    const r1 = await app.inject({ method: 'GET', url: '/claims/count', query });
    expect(r1.statusCode).toBe(200);
    const body1 = r1.json() as { dataset_version: string; query_hash: string; n: number; samples: string[] };
    expect(body1.dataset_version).toBe('d1-test');
    expect(body1.query_hash).toBe(expectedHash);
    expect(body1.n).toBe(12);
    expect(body1.samples.length).toBeGreaterThanOrEqual(10);
    expect(new Set(body1.samples).size).toBeGreaterThanOrEqual(10);

    const r2 = await app.inject({ method: 'GET', url: '/claims/count', query });
    expect(r2.statusCode).toBe(200);
    expect(r2.json()).toEqual(body1);
  });
});
