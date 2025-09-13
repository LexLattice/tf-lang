import type { Filters, Claim, CountResult, ListResult, Evidence } from './types.js';
import { queryHash } from './util.js';
import { buildDb } from '@tf-lang/d1-sqlite';
import type { Database } from 'sql.js';

interface Stmt {
  bind(params: unknown[]): void;
  step(): boolean;
  getAsObject(): Record<string, unknown>;
  reset(): void;
}

export interface ClaimDb {
  db: Database;
  datasetVersion: string;
  countStmt: Stmt;
  sampleStmt: Stmt;
  listStmt: Stmt;
  claimStmt: Stmt;
}

let memo: ClaimDb | null = null;
export function openDb(): ClaimDb {
  if (!memo) {
    try {
      const db = buildDb();
      const res = db.exec("SELECT value FROM meta WHERE key='dataset_version';");
      const datasetVersion = res[0]?.values?.[0]?.[0];
      if (typeof datasetVersion !== 'string') throw new Error('bad_dataset_version');
      const where =
        [
          'WHERE (?1 IS NULL OR modality = ?1)',
          '(?2 IS NULL OR jurisdiction = ?2)',
          "(?3 IS NULL OR (effective_from <= ?3 AND (?3 <= IFNULL(effective_to, '9999-12-31'))))",
        ].join(' AND ');
      memo = {
        db,
        datasetVersion,
        countStmt: db.prepare(`SELECT COUNT(*) as c FROM claims ${where};`),
        sampleStmt: db.prepare(
          `SELECT DISTINCT json_extract(data,'$.evidence[0]') as ev FROM claims ${where} ORDER BY id LIMIT 10;`
        ),
        listStmt: db.prepare(`SELECT data FROM claims ${where} ORDER BY id LIMIT ?4 OFFSET ?5;`),
        claimStmt: db.prepare('SELECT data FROM claims WHERE id = ?1;'),
      };
    } catch {
      throw new Error('db_init_failed');
    }
  }
  return memo;
}

function paramsFromFilters(f: Filters): unknown[] {
  return [f.modality ?? null, f.jurisdiction ?? null, f.at ?? null];
}

function runAll<T>(stmt: Stmt, map: (row: Record<string, unknown>) => T | undefined): T[] {
  const out: T[] = [];
  while (stmt.step()) {
    const mapped = map(stmt.getAsObject());
    if (mapped !== undefined) out.push(mapped);
  }
  stmt.reset();
  return out;
}

export function count(db: ClaimDb, f: Filters): CountResult {
  const params = paramsFromFilters(f);
  const stmt = db.countStmt;
  stmt.bind(params);
  stmt.step();
  const row = stmt.getAsObject();
  const n = typeof row.c === 'number' ? row.c : 0;
  stmt.reset();
  const evStmt = db.sampleStmt;
  evStmt.bind(params);
  const samples = runAll(evStmt, r => {
    const v = r.ev;
    if (typeof v !== 'string') return undefined;
    return JSON.parse(v) as Evidence;
  });
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
  const params = paramsFromFilters(f);
  const totalStmt = db.countStmt;
  totalStmt.bind(params);
  totalStmt.step();
  const tRow = totalStmt.getAsObject();
  const total = typeof tRow.c === 'number' ? tRow.c : 0;
  totalStmt.reset();
  const listStmt = db.listStmt;
  listStmt.bind([...params, limit, offset]);
  const items = runAll(listStmt, r => {
    const v = r.data;
    if (typeof v !== 'string') return undefined;
    return JSON.parse(v) as Claim;
  });
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
  const stmt = db.claimStmt;
  stmt.bind([id]);
  const rows = runAll(stmt, r => {
    const v = r.data;
    if (typeof v !== 'string') return undefined;
    return JSON.parse(v) as Claim;
  });
  return rows[0] ?? null;
}
