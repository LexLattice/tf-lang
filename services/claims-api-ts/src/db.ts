import { buildDb } from '@tf-lang/d1-sqlite';
import type { Database } from 'sql.js';
import { queryHash } from './util.js';
import type { Claim, CountResult, Evidence, Filters, ListResult } from './types.js';

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

function whereParams(f: Filters): { clause: string; params: unknown[] } {
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
    clauses.push('effective_from <= ? AND ? <= IFNULL(effective_to, \"9999-12-31\")');
    params.push(f.at, f.at);
  }
  return { clause: clauses.length ? 'WHERE ' + clauses.join(' AND ') : '', params };
}

export function count(db: ClaimDb, f: Filters): CountResult {
  const { clause, params } = whereParams(f);
  const stmt = db.db.prepare(`SELECT data FROM claims ${clause} ORDER BY id;`);
  stmt.bind(params);
  const rows: string[] = [];
  while (stmt.step()) rows.push(stmt.get()[0] as string);
  stmt.free();
  const evidences: Evidence[] = [];
  const seen = new Set<string>();
  for (const raw of rows) {
    const claim = JSON.parse(raw) as Claim;
    for (const e of claim.evidence) {
      if (!seen.has(e.hash)) {
        evidences.push(e);
        seen.add(e.hash);
        if (evidences.length >= 10) break;
      }
    }
    if (evidences.length >= 10) break;
  }
  return {
    dataset_version: db.datasetVersion,
    query_hash: queryHash(f as Record<string, unknown>),
    filters: f,
    n: rows.length,
    samples: evidences,
  };
}

export function list(db: ClaimDb, f: Filters): ListResult {
  const { clause, params } = whereParams(f);
  const offset = Math.max(0, Math.floor(f.offset ?? 0));
  const limit0 = Math.floor(f.limit ?? 10);
  const limit = Math.min(Math.max(1, limit0), 200);
  const stmt = db.db.prepare(
    `SELECT data FROM claims ${clause} ORDER BY id LIMIT ? OFFSET ?;`,
  );
  stmt.bind([...params, limit, offset]);
  const items: Claim[] = [];
  while (stmt.step()) items.push(JSON.parse(stmt.get()[0] as string) as Claim);
  stmt.free();
  const totalStmt = db.db.prepare(`SELECT COUNT(*) FROM claims ${clause};`);
  totalStmt.bind(params);
  totalStmt.step();
  const total = totalStmt.get()[0] as number;
  totalStmt.free();
  const filters: Filters = { ...f, limit, offset };
  return {
    dataset_version: db.datasetVersion,
    query_hash: queryHash(filters as Record<string, unknown>),
    filters,
    total,
    items,
  };
}

export function getClaim(db: ClaimDb, id: string): Claim | null {
  const stmt = db.db.prepare('SELECT data FROM claims WHERE id = ?;');
  stmt.bind([id]);
  const row = stmt.step() ? (stmt.get()[0] as string) : null;
  stmt.free();
  return row ? (JSON.parse(row) as Claim) : null;
}

