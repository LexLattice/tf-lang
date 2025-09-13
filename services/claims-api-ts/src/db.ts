import type { Filters, Claim, CountResult, ListResult, Evidence } from './types.js';
import { queryHash } from './util.js';
import { buildDb } from '@tf-lang/d1-sqlite';
import type { Database, Statement } from 'sql.js';

export interface ClaimDb {
  db: Database;
  datasetVersion: string;
  countStmt: Statement;
  sampleStmt: Statement;
  listStmt: Statement;
  getStmt: Statement;
}

let memo: ClaimDb | null = null;
export function openDb(): ClaimDb {
  if (!memo) {
    const db = buildDb();
    const res = db.exec("SELECT value FROM meta WHERE key='dataset_version';");
    const datasetVersion = res[0]?.values[0][0] as string;
    const baseWhere =
      "WHERE (?1 IS NULL OR modality = ?1) AND (?2 IS NULL OR jurisdiction = ?2) AND (?3 IS NULL OR (effective_from <= ?3 AND (?3 <= IFNULL(effective_to, '9999-12-31'))))";
    memo = {
      db,
      datasetVersion,
      countStmt: db.prepare(`SELECT COUNT(*) as c FROM claims ${baseWhere};`),
      sampleStmt: db.prepare(
        `SELECT DISTINCT json_extract(data,'$.evidence[0]') as ev FROM claims ${baseWhere} ORDER BY id LIMIT 10;`
      ),
      listStmt: db.prepare(
        `SELECT data FROM claims ${baseWhere} ORDER BY id LIMIT ?4 OFFSET ?5;`
      ),
      getStmt: db.prepare('SELECT data FROM claims WHERE id = ?1;'),
    };
  }
  return memo;
}

function runAll<T>(stmt: Statement, params: unknown[], map: (row: Record<string, unknown>) => T): T[] {
  stmt.bind(params);
  const out: T[] = [];
  while (stmt.step()) {
    out.push(map(stmt.getAsObject()));
  }
  stmt.reset();
  return out;
}

function runCount(stmt: Statement, params: unknown[]): number {
  stmt.bind(params);
  stmt.step();
  const n = (stmt.getAsObject().c as number) || 0;
  stmt.reset();
  return n;
}

export function count(db: ClaimDb, f: Filters): CountResult {
  const params = [f.modality ?? null, f.jurisdiction ?? null, f.at ?? null];
  const n = runCount(db.countStmt, params);
  const samples = runAll(db.sampleStmt, params, r => JSON.parse(r.ev as string) as Evidence);
  return {
    dataset_version: db.datasetVersion,
    query_hash: queryHash(f),
    filters: f,
    n,
    samples,
  };
}

export function list(db: ClaimDb, f: Filters): ListResult {
  const limit = f.limit ?? 10;
  const offset = f.offset ?? 0;
  const baseParams = [f.modality ?? null, f.jurisdiction ?? null, f.at ?? null];
  const total = runCount(db.countStmt, baseParams);
  const items = runAll(db.listStmt, [...baseParams, limit, offset], r => JSON.parse(r.data as string) as Claim);
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
  const rows = runAll(db.getStmt, [id], r => JSON.parse(r.data as string) as Claim);
  return rows[0] ?? null;
}

