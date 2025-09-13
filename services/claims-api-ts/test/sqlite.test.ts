import { describe, it, expect } from 'vitest';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import initSqlJs from 'sql.js';
import { fileURLToPath } from 'node:url';
import { ClaimsDB } from '../src/db.js';
import { queryHash } from '../src/util.js';

const __dirname = path.dirname(fileURLToPath(import.meta.url));

async function makeDb(): Promise<string> {
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'claims-'));
  const dbPath = path.join(tmp, 'claims.db');
  const SQL = await initSqlJs();
  const db = new SQL.Database();
  db.run(`CREATE TABLE meta (key TEXT PRIMARY KEY, value TEXT);`);
  db.run(`CREATE TABLE claims (
    id TEXT PRIMARY KEY,
    kind TEXT,
    modality TEXT,
    jurisdiction TEXT,
    effective_from TEXT,
    effective_to TEXT,
    claim_json TEXT
  );`);
  const raw = fs.readFileSync(path.join(__dirname, '..', 'data', 'claims.json'), 'utf-8');
  const data = JSON.parse(raw);
  db.run(`INSERT INTO meta(key,value) VALUES ('dataset_version', ?)`, [data.dataset_version]);
  const stmt = db.prepare(`INSERT INTO claims (id, kind, modality, jurisdiction, effective_from, effective_to, claim_json) VALUES ($id, $kind, $modality, $jurisdiction, $effective_from, $effective_to, $claim_json)`);
  for (let i = 0; i < 12; i++) {
    const base = data.claims[i % data.claims.length];
    stmt.run({
      $id: `C${i}`,
      $kind: base.kind,
      $modality: base.modality,
      $jurisdiction: base.scope.jurisdiction ?? null,
      $effective_from: base.effective.from,
      $effective_to: base.effective.to ?? null,
      $claim_json: JSON.stringify({ ...base, id: `C${i}` }),
    });
  }
  stmt.free();
  const binary = db.export();
  fs.writeFileSync(dbPath, Buffer.from(binary));
  return dbPath;
}

describe('sqlite adapter', () => {
  it('hashes, counts, samples stable via sqlite', async () => {
    const dbPath = await makeDb();
    const db = await ClaimsDB.open(dbPath);
    const filters = {};
    const expectedHash = queryHash(filters);
    const r1 = db.count(filters);
    const r2 = db.count(filters);
    expect(db.datasetVersion).toBe('ro-mini-2025-09-09');
    expect(queryHash(filters)).toBe(expectedHash);
    expect(r1).toEqual(r2);
    expect(r1.samples.length).toBeGreaterThanOrEqual(10);
    const distinct = new Set(r1.samples);
    expect(distinct.size).toBe(r1.samples.length);
  });
});
