import type { Filters, Claim, Evidence, CountResponse, ListResponse } from './types.js';
import { queryHash } from './util.js';
import { buildDb } from '@tf-lang/d1-sqlite';
import type { Database, Statement } from 'sql.js';

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

interface WhereFrag {
  sql: string;
  params: unknown[];
}

function buildWhere(f: Filters): WhereFrag {
  const clauses: string[] = [];
  const params: unknown[] = [];
  if (f.modality) { clauses.push('modality = ?'); params.push(f.modality); }
  if (f.jurisdiction) { clauses.push('jurisdiction = ?'); params.push(f.jurisdiction); }
  if (f.at) {
    clauses.push('effective_from <= ? AND ? <= IFNULL(effective_to, \"9999-12-31\")');
    params.push(f.at, f.at);
  }
  const sql = clauses.length ? 'WHERE ' + clauses.join(' AND ') : '';
  return { sql, params };
}

function all<T>(stmt: Statement, mapper: (row: unknown[]) => T): T[] {
  const out: T[] = [];
  while (stmt.step()) out.push(mapper(stmt.get()));
  stmt.free();
  return out;
}

export function count(db: ClaimDb, f: Filters): CountResponse {
  const { sql, params } = buildWhere(f);
  const countStmt = db.db.prepare(`SELECT COUNT(*) FROM claims ${sql};`);
  countStmt.bind(params);
  countStmt.step();
  const n = countStmt.get()[0] as number;
  countStmt.free();

  const sampleStmt = db.db.prepare(`SELECT data FROM claims ${sql} ORDER BY id LIMIT 100;`);
  sampleStmt.bind(params);
  const evidences: Evidence[] = [];
  const seen = new Set<string>();
  while (sampleStmt.step() && evidences.length < 10) {
    const claim = JSON.parse(sampleStmt.get()[0] as string) as Claim;
    const ev = claim.evidence?.[0];
    if (ev && !seen.has(ev.hash)) { seen.add(ev.hash); evidences.push(ev); }
  }
  sampleStmt.free();

  return {
    dataset_version: db.datasetVersion,
    query_hash: queryHash(f),
    filters: f,
    n,
    samples: evidences,
  };
}

export function list(db: ClaimDb, f: Filters): ListResponse {
  const { sql, params } = buildWhere(f);
  const offset = Number.isFinite(f.offset) ? Math.max(0, Number(f.offset)) : 0;
  const limit0 = Number.isFinite(f.limit) ? Number(f.limit) : 10;
  const limit = Math.min(Math.max(1, limit0), 200);

  const itemsStmt = db.db.prepare(`SELECT data FROM claims ${sql} ORDER BY id LIMIT ? OFFSET ?;`);
  itemsStmt.bind([...params, limit, offset]);
  const items = all(itemsStmt, r => JSON.parse(r[0] as string) as Claim);

  const totalStmt = db.db.prepare(`SELECT COUNT(*) FROM claims ${sql};`);
  totalStmt.bind(params);
  totalStmt.step();
  const total = totalStmt.get()[0] as number;
  totalStmt.free();

  const responseFilters: Filters = { ...f, offset, limit };
  return {
    dataset_version: db.datasetVersion,
    query_hash: queryHash(responseFilters),
    filters: responseFilters,
    total,
    items,
  };
}

export function getClaim(db: ClaimDb, id: string): Claim | null {
  const stmt = db.db.prepare('SELECT data FROM claims WHERE id = ?;');
  stmt.bind([id]);
  const ok = stmt.step();
  const row = ok ? stmt.get()[0] : null;
  stmt.free();
  return row ? (JSON.parse(row as string) as Claim) : null;
}
