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
    const db = buildDb();
    const res = db.exec("SELECT value FROM meta WHERE key='dataset_version';");
    const datasetVersion = res[0]?.values[0]?.[0];
    if (typeof datasetVersion !== 'string') throw new Error('missing_dataset_version');
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
  }
  return memo;
}

function paramsFromFilters(f: Filters): unknown[] {
  return [f.modality ?? null, f.jurisdiction ?? null, f.at ?? null];
}

function runAll<T>(stmt: Stmt, map: (row: Record<string, unknown>) => T): T[] {
  const out: T[] = [];
  while (stmt.step()) {
    out.push(map(stmt.getAsObject()));
  }
  stmt.reset();
  return out;
}

function parseEvidence(row: Record<string, unknown>): Evidence {
  const ev = row.ev;
  if (typeof ev !== 'string') throw new Error('bad_evidence_row');
  return JSON.parse(ev) as Evidence;
}

function parseClaim(row: Record<string, unknown>): Claim {
  const data = row.data;
  if (typeof data !== 'string') throw new Error('bad_claim_row');
  return JSON.parse(data) as Claim;
}

export function count(db: ClaimDb, f: Filters): CountResult {
  const params = paramsFromFilters(f);
  const stmt = db.countStmt;
  stmt.bind(params);
  stmt.step();
  const cVal = stmt.getAsObject().c;
  const n = typeof cVal === 'number' ? cVal : 0;
  stmt.reset();
  const evStmt = db.sampleStmt;
  evStmt.bind(params);
  const samples = runAll(evStmt, parseEvidence);
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
  const tVal = totalStmt.getAsObject().c;
  const total = typeof tVal === 'number' ? tVal : 0;
  totalStmt.reset();
  const listStmt = db.listStmt;
  listStmt.bind([...params, limit, offset]);
  const items = runAll(listStmt, parseClaim);
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
  const rows = runAll(stmt, parseClaim);
  return rows[0] ?? null;
}
