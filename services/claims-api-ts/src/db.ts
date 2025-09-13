import type { Filters, CountResponse, ListResponse, Claim, Evidence } from './types.js';
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
    const stmt = db.prepare("SELECT value FROM meta WHERE key='dataset_version';");
    stmt.step();
    const datasetVersion = stmt.getAsObject<{ value: string }>().value;
    stmt.free();
    memo = { db, datasetVersion };
  }
  return memo;
}

interface Where {
  clause: string;
  params: unknown[];
}
function buildWhere(f: Filters): Where {
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

function collectSamples(stmt: Statement): Evidence[] {
  const out: Evidence[] = [];
  const seen = new Set<string>();
  while (stmt.step() && out.length < 10) {
    const row = stmt.getAsObject<{ data: string }>();
    const obj = JSON.parse(row.data) as unknown;
    const claim = obj as { evidence?: unknown[] };
    if (Array.isArray(claim.evidence) && claim.evidence[0] && typeof claim.evidence[0] === 'object') {
      const ev = claim.evidence[0] as Record<string, unknown>;
      const hash = typeof ev.hash === 'string' ? ev.hash : '';
      if (hash && !seen.has(hash)) {
        out.push({
          source_uri: String(ev.source_uri || ''),
          span: ev.span ?? null,
          hash,
          rule_id: typeof ev.rule_id === 'string' ? ev.rule_id : undefined,
        });
        seen.add(hash);
      }
    }
  }
  stmt.free();
  return out;
}

export function count(db: ClaimDb, f: Filters): CountResponse {
  const where = buildWhere(f);
  const countStmt = db.db.prepare(`SELECT COUNT(*) as n FROM claims ${where.clause};`);
  countStmt.bind(where.params);
  countStmt.step();
  const n = Number(countStmt.getAsObject<{ n: number }>().n);
  countStmt.free();

  const sampleStmt = db.db.prepare(`SELECT data FROM claims ${where.clause} ORDER BY id LIMIT 100;`);
  sampleStmt.bind(where.params);
  const samples = collectSamples(sampleStmt);

  return {
    dataset_version: db.datasetVersion,
    query_hash: queryHash(f),
    filters: f,
    n,
    samples,
  };
}

export function list(db: ClaimDb, f: Filters): ListResponse {
  const offset = Number.isFinite(f.offset) ? Math.max(0, Number(f.offset)) : 0;
  const limit0 = Number.isFinite(f.limit) ? Number(f.limit) : 10;
  const limit = Math.min(Math.max(1, limit0), 200);
  const where = buildWhere(f);

  const listStmt = db.db.prepare(`SELECT data FROM claims ${where.clause} ORDER BY id LIMIT ? OFFSET ?;`);
  listStmt.bind([...where.params, limit, offset]);
  const items: Claim[] = [];
  while (listStmt.step()) {
    const row = listStmt.getAsObject<{ data: string }>();
    items.push(JSON.parse(row.data) as Claim);
  }
  listStmt.free();

  const countStmt = db.db.prepare(`SELECT COUNT(*) as n FROM claims ${where.clause};`);
  countStmt.bind(where.params);
  countStmt.step();
  const total = Number(countStmt.getAsObject<{ n: number }>().n);
  countStmt.free();

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
  const item = stmt.step() ? (JSON.parse(stmt.getAsObject<{ data: string }>().data) as Claim) : null;
  stmt.free();
  return item;
}
