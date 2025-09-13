import { spawnSync } from 'node:child_process';
import type { Claim } from 'claims-core-ts';

export interface Filters {
  modality?: string;
  jurisdiction?: string;
  at?: string; // ISO date
}

export interface LegalDb {
  path: string;
  datasetVersion: string;
}

function run(dbPath: string, sql: string): string[] {
  const out = spawnSync('sqlite3', ['-readonly', '-noheader', dbPath, sql], { encoding: 'utf-8' });
  const s = out.stdout.trim();
  return s ? s.split('\n') : [];
}

export function open(dbPath: string): LegalDb {
  const v = run(dbPath, "SELECT value FROM meta WHERE key='dataset_version';")[0];
  return { path: dbPath, datasetVersion: v ?? 'dev' };
}

function where(f: Filters): string {
  const clauses: string[] = [];
  if (f.modality) clauses.push(`modality='${f.modality}'`);
  if (f.jurisdiction) clauses.push(`jurisdiction='${f.jurisdiction}'`);
  if (f.at) clauses.push(`effective_from <= '${f.at}' AND ('${f.at}' <= IFNULL(effective_to,'\uFFFF'))`);
  return clauses.length ? `WHERE ${clauses.join(' AND ')}` : '';
}

function rowToClaim(j: string): Claim {
  const r = JSON.parse(j);
  return {
    id: r.id,
    kind: r.kind,
    modality: r.modality,
    scope: { jurisdiction: r.jurisdiction },
    effective: { from: r.effective_from, to: r.effective_to ?? null },
    status: r.status,
    explanation: undefined,
    evidence: JSON.parse(r.evidence),
    dataset_version: '',
    query_hash: '',
  };
}

function rows(db: LegalDb, w: string): Claim[] {
  const sql = `SELECT json_object('id',id,'kind',kind,'modality',modality,'jurisdiction',jurisdiction,'effective_from',effective_from,'effective_to',effective_to,'evidence',evidence,'status',status) FROM claims ${w} ORDER BY id;`;
  return run(db.path, sql).map(rowToClaim);
}

export function count(db: LegalDb, f: Filters) {
  const ids = run(db.path, `SELECT id FROM claims ${where(f)} ORDER BY id;`);
  return { n: ids.length, samples: ids.slice(0, 10) };
}

export function list(db: LegalDb, f: Filters) {
  return { items: rows(db, where(f)) };
}

export function getById(db: LegalDb, id: string): Claim | undefined {
  return rows(db, `WHERE id='${id}'`)[0];
}
