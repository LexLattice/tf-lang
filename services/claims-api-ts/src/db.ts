import type { Filters, Claim, CountResult, ListResult, Evidence } from './types.js';
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

interface Stmt {
  bind(params: unknown[]): void;
  step(): boolean;
  getAsObject(): Record<string, unknown>;
  free(): void;
}

function runAll<T>(stmt: Stmt, map: (row: Record<string, unknown>) => T): T[] {
  const out: T[] = [];
  while (stmt.step()) {
    out.push(map(stmt.getAsObject()));
  }
  stmt.free();
  return out;
}

export function count(db: ClaimDb, f: Filters): CountResult {
  const { sql, params } = buildWhere(f);
  const stmt = db.db.prepare(`SELECT COUNT(*) as c FROM claims ${sql};`);
  stmt.bind(params);
  stmt.step();
  const n = (stmt.getAsObject().c as number) || 0;
  stmt.free();
  const evStmt = db.db.prepare(
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
  const offset = Number.isFinite(f.offset) ? Math.max(0, Math.floor(f.offset as number)) : 0;
  const limit0 = Number.isFinite(f.limit) ? Math.floor(f.limit as number) : 10;
  const limit = Math.min(Math.max(1, limit0), 200);
  const { sql, params } = buildWhere(f);
  const totalStmt = db.db.prepare(`SELECT COUNT(*) as c FROM claims ${sql};`);
  totalStmt.bind(params);
  totalStmt.step();
  const total = (totalStmt.getAsObject().c as number) || 0;
  totalStmt.free();
  const listStmt = db.db.prepare(
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
  const stmt = db.db.prepare('SELECT data FROM claims WHERE id = ?;');
  stmt.bind([id]);
  const rows = runAll(stmt, r => JSON.parse(r.data as string) as Claim);
  return rows[0] ?? null;
}
