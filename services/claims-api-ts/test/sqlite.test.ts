import { describe, it, expect } from 'vitest';
import { execSync } from 'node:child_process';
import path from 'node:path';
import fs from 'node:fs';
import os from 'node:os';
import { buildServer } from '../src/server.js';
import { queryHash } from '../src/util.js';

function run(sql: string, file: string) {
  execSync(`sqlite3 ${file} "${sql}"`);
}

function createDb(): string {
  const file = path.join(os.tmpdir(), `claims-${Date.now()}.db`);
  run('create table meta(key text primary key, value text);', file);
  run("insert into meta(key,value) values ('dataset_version','test-1');", file);
  run('create table claims(id text primary key, kind text, modality text, jurisdiction text, effective_from text, effective_to text, evidence text, status text);', file);
  for (let i=1;i<=12;i++) {
    run(`insert into claims values ('C${i}','DEONTIC','FORBIDDEN','RO','2024-01-01',NULL,'${JSON.stringify([{ source_uri: `src${i}`, span: null, hash: String(i), rule_id: 'r1' }]).replace(/'/g, "''")}','determinate');`, file);
  }
  return file;
}

describe('D1 SQLite adapter', () => {
  it('returns stable counts with query hash and ≥10 samples', async () => {
    const dbPath = createDb();
    const app = buildServer(dbPath);

    const params = { modality: 'FORBIDDEN', jurisdiction: 'RO', at: '2024-02-02' };
    const qs = new URLSearchParams(params as any).toString();
    const expectedHash = queryHash(params);

    const res1 = await app.inject(`/claims/count?${qs}`);
    expect(res1.statusCode).toBe(200);
    const body1 = res1.json();
    expect(body1.dataset_version).toBe('test-1');
    expect(body1.query_hash).toBe(expectedHash);
    expect(body1.samples.length).toBeGreaterThanOrEqual(10);

    const res2 = await app.inject(`/claims/count?${qs}`);
    expect(res2.json()).toEqual(body1);

    const list1 = await app.inject(`/claims/list?${qs}`);
    const listBody1 = list1.json();

    const list2 = await app.inject(`/claims/list?${qs}`);
    expect(list2.json()).toEqual(listBody1);

    await app.close();
    fs.unlinkSync(dbPath);
  });
});
