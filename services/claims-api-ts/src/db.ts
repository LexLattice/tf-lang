import type { Filters, Claim, CountResult, ListResult, Evidence } from './types.js';
import { queryHash } from './util.js';
import { buildDb } from '@tf-lang/d1-sqlite';
import type { Database, Statement } from 'sql.js';

export interface ClaimDb {
  db: Database;
  datasetVersion: string;
  stmts: Map<string, Statement>;
}

let memo: ClaimDb | null = null;
export function openDb(): ClaimDb {
  if (!memo) {
    const db = buildDb();
    const res = db.exec("SELECT value FROM meta WHERE key='dataset_version';");
    const datasetVersion = res[0]?.values[0][0] as string;
    memo = { db, datasetVersion, stmts: new Map() };
  }
  return memo;
}

function buildWhere(f: Filters): { sql: string; params: unknown[] } {
  const clauses: string[] = [];
  const params: unknown[] = [];
  if (f.modality) {
    clauses.push('modality = ?');
    params.push(f.modality);
  }
  if (f.jurisdiction) {
    clauses.push('jurisdiction = ?');
    params.push(f.jurisdiction);
  }
  if (f.at) {
    clauses.push("effective_from <= ? AND (? <= IFNULL(effective_to, '9999-12-31'))");
    params.push(f.at, f.at);
  }
  return { sql: clauses.length ? 'WHERE ' + clauses.join(' AND ') : '', params };
}

function prepare(db: ClaimDb, sql: string): Statement {
  const existing = db.stmts.get(sql);
  if (existing) {
    existing.reset();
    return existing;
  }
  const stmt = db.db.prepare(sql);
  db.stmts.set(sql, stmt);
  return stmt;
}

function runAll<T>(stmt: Statement, map: (row: Record<string, unknown>) => T): T[] {
  const out: T[] = [];
  while (stmt.step()) {
    out.push(map(stmt.getAsObject()));
  }
  stmt.reset();
  return out;
}

export function count(db: ClaimDb, f: Filters): CountResult {
  const { sql, params } = buildWhere(f);
  const stmt = prepare(db, `SELECT COUNT(*) as c FROM claims ${sql};`);
  stmt.bind(params);
  stmt.step();
  const n = (stmt.getAsObject().c as number) || 0;
  stmt.reset();
  const evStmt = prepare(
    db,
    `SELECT DISTINCT json_extract(data,'$.evidence[0]') as ev FROM claims ${sql} ORDER BY id LIMIT 10;`
  );
  evStmt.bind(params);
  const samples = runAll(evStmt, r => JSON.parse(r.ev as string) as Evidence);
  return {
    dataset_version: db.datasetVersion,
    query_hash: queryHash(f),
    filters: f,
    n,
    samples,
  };
}

export function list(db: ClaimDb, f: Filters): ListResult {
  const offset = f.offset ?? 0;
  const limit = f.limit ?? 10;
  const { sql, params } = buildWhere(f);
  const totalStmt = prepare(db, `SELECT COUNT(*) as c FROM claims ${sql};`);
  totalStmt.bind(params);
  totalStmt.step();
  const total = (totalStmt.getAsObject().c as number) || 0;
  totalStmt.reset();
  const listStmt = prepare(
    db,
    `SELECT data FROM claims ${sql} ORDER BY id LIMIT ? OFFSET ?;`
  );
  listStmt.bind([...params, limit, offset]);
  const items = runAll(listStmt, r => JSON.parse(r.data as string) as Claim);
  const responseFilters: Filters = { ...f, limit, offset };
  return {
    dataset_version: db.datasetVersion,
    query_hash: queryHash(responseFilters),
    filters: responseFilters,
    total,
    items,
  };
}

export function getClaim(db: ClaimDb, id: string): Claim | null {
  const stmt = prepare(db, 'SELECT data FROM claims WHERE id = ?;');
  stmt.bind([id]);
  const rows = runAll(stmt, r => JSON.parse(r.data as string) as Claim);
  return rows[0] ?? null;
}
