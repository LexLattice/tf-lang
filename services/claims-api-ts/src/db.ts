import type { Filters } from './types.js';
import { queryHash } from './util.js';
import { buildDb } from '@tf-lang/d1-sqlite';
import type { Database } from 'sql.js';

export interface ClaimDb {
  db: Database;
  datasetVersion: string;
}

let memo: ClaimDb | null = null;
export function openDb(): ClaimDb {
  if (!memo) {
    const db = buildDb();
    const res = db.exec("SELECT value FROM meta WHERE key='dataset_version';");
    const datasetVersion = res[0]?.values[0][0] as string;
    memo = { db, datasetVersion };
  }
  return memo;
}

function quote(x: string): string {
  return `'${x.replace(/'/g, "''")}'`;
}

function whereClause(f: Filters): string {
  const clauses: string[] = [];
  if (f.modality) clauses.push(`modality = ${quote(f.modality)}`);
  if (f.jurisdiction) clauses.push(`jurisdiction = ${quote(f.jurisdiction)}`);
  if (f.at) clauses.push(`effective_from <= ${quote(f.at)} AND (${quote(f.at)} <= IFNULL(effective_to, '9999-12-31'))`);
  return clauses.length ? 'WHERE ' + clauses.join(' AND ') : '';
}

export function count(db: ClaimDb, f: Filters) {
  const where = whereClause(f);
  const rows = db.db.exec(`SELECT data FROM claims ${where} ORDER BY id;`)[0]?.values ?? [];
  const evidences: any[] = [];
  for (const r of rows.slice(0, 10)) {
    const claim = JSON.parse(r[0] as string);
    if (claim.evidence && claim.evidence[0]) evidences.push(claim.evidence[0]);
  }
  return {
    dataset_version: db.datasetVersion,
    query_hash: queryHash(f),
    filters: f,
    n: rows.length,
    samples: evidences,
  };
}

export function list(db: ClaimDb, f: Filters) {
  const where = whereClause(f);
  const rows = db.db.exec(`SELECT data FROM claims ${where} ORDER BY id;`)[0]?.values ?? [];
  const offset = Number.isFinite(f.offset) ? Math.max(0, Number(f.offset)) : 0;
  const limit0 = Number.isFinite(f.limit) ? Number(f.limit) : 10;
  const limit = Math.min(Math.max(1, limit0), 200);
  const items = rows.slice(offset, offset + limit).map(r => JSON.parse(r[0] as string));
  const responseFilters: Filters = { ...f, offset, limit };
  return {
    dataset_version: db.datasetVersion,
    query_hash: queryHash(responseFilters),
    filters: responseFilters,
    total: rows.length,
    items,
  };
}

export function getClaim(db: ClaimDb, id: string) {
  const rows = db.db.exec(`SELECT data FROM claims WHERE id = ${quote(id)};`)[0]?.values ?? [];
  return rows[0] ? JSON.parse(rows[0][0] as string) : null;
}
