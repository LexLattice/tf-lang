import type { Filters, Claim, CountResult, ListResult, Evidence } from './types.js';
import { queryHash } from './util.js';
import { buildDb } from '@tf-lang/d1-sqlite';
import type { Database, Statement } from 'sql.js';

export interface ClaimDb {
  db: Database;
  datasetVersion: string;
  stmts: {
    count: Statement;
    sample: Statement;
    list: Statement;
    total: Statement;
    getClaim: Statement;
  };
}

let memo: ClaimDb | null = null;
export function openDb(): ClaimDb {
  if (!memo) {
    const db = buildDb();
    const res = db.exec("SELECT value FROM meta WHERE key='dataset_version';");
    const datasetVersion = res[0]?.values[0][0] as string;
    const baseWhere =
      "(? IS NULL OR modality = ?) AND (? IS NULL OR jurisdiction = ?) AND (? IS NULL OR (effective_from <= ? AND (? <= IFNULL(effective_to, '9999-12-31'))))";
    const countSql = `SELECT COUNT(*) as c FROM claims WHERE ${baseWhere};`;
    const sampleSql =
      `SELECT DISTINCT json_extract(data,'$.evidence[0]') as ev FROM claims WHERE ${baseWhere} ORDER BY id LIMIT 10;`;
    const listSql =
      `SELECT data FROM claims WHERE ${baseWhere} ORDER BY id LIMIT ? OFFSET ?;`;
    memo = {
      db,
      datasetVersion,
      stmts: {
        count: db.prepare(countSql),
        sample: db.prepare(sampleSql),
        list: db.prepare(listSql),
        total: db.prepare(countSql),
        getClaim: db.prepare('SELECT data FROM claims WHERE id = ?;'),
      },
    };
  }
  return memo;
}

function filterParams(f: Filters): unknown[] {
  return [
    f.modality ?? null,
    f.modality ?? null,
    f.jurisdiction ?? null,
    f.jurisdiction ?? null,
    f.at ?? null,
    f.at ?? null,
    f.at ?? null,
  ];
}

function collectAll<T>(stmt: Statement, map: (row: Record<string, unknown>) => T): T[] {
  const out: T[] = [];
  while (stmt.step()) {
    out.push(map(stmt.getAsObject()));
  }
  stmt.reset();
  return out;
}

export function count(db: ClaimDb, f: Filters): CountResult {
  const params = filterParams(f);
  db.stmts.count.bind(params);
  db.stmts.count.step();
  const n = (db.stmts.count.getAsObject().c as number) || 0;
  db.stmts.count.reset();

  db.stmts.sample.bind(params);
  const samples = collectAll(db.stmts.sample, r => JSON.parse(r.ev as string) as Evidence);
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
  const params = filterParams(f);

  db.stmts.total.bind(params);
  db.stmts.total.step();
  const total = (db.stmts.total.getAsObject().c as number) || 0;
  db.stmts.total.reset();

  db.stmts.list.bind([...params, limit, offset]);
  const items = collectAll(db.stmts.list, r => JSON.parse(r.data as string) as Claim);
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
  db.stmts.getClaim.bind([id]);
  const rows = collectAll(db.stmts.getClaim, r => JSON.parse(r.data as string) as Claim);
  return rows[0] ?? null;
}
