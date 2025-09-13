import fs from 'node:fs';
import initSqlJs, { Database } from 'sql.js';
import type { Claim } from 'claims-core-ts';
import type { Filters } from './types.js';

export class ClaimsDB {
  private db: Database;
  datasetVersion: string;

  private constructor(db: Database, version: string) {
    this.db = db;
    this.datasetVersion = version;
  }

  static async open(filename: string): Promise<ClaimsDB> {
    const SQL = await initSqlJs();
    const file = fs.readFileSync(filename);
    const db = new SQL.Database(file);
    const res = db.exec("SELECT value FROM meta WHERE key='dataset_version'");
    const version = (res[0]?.values[0]?.[0] as string) || 'dev';
    return new ClaimsDB(db, version);
  }

  count(f: Filters) {
    const w = this.buildWhere(f);
    const stmtC = this.db.prepare(`SELECT COUNT(*) as n FROM claims ${w.sql}`);
    stmtC.bind(w.params);
    stmtC.step();
    const n = stmtC.getAsObject().n as number;
    stmtC.free();
    const stmtS = this.db.prepare(`SELECT id FROM claims ${w.sql} ORDER BY id LIMIT 10`);
    stmtS.bind(w.params);
    const samples: string[] = [];
    while (stmtS.step()) {
      const row = stmtS.getAsObject() as { id: string };
      samples.push(row.id);
    }
    stmtS.free();
    return { n, samples };
  }

  list(f: Filters) {
    const offset = Math.max(0, f.offset ?? 0);
    const limit = Math.min(Math.max(1, f.limit ?? 10), 200);
    const w = this.buildWhere(f);
    const stmtT = this.db.prepare(`SELECT COUNT(*) as n FROM claims ${w.sql}`);
    stmtT.bind(w.params);
    stmtT.step();
    const total = stmtT.getAsObject().n as number;
    stmtT.free();
    const stmtI = this.db.prepare(`SELECT claim_json FROM claims ${w.sql} ORDER BY id LIMIT $limit OFFSET $offset`);
    stmtI.bind({ ...w.params, $limit: limit, $offset: offset });
    const items: Claim[] = [];
    while (stmtI.step()) {
      const row = stmtI.getAsObject() as { claim_json: string };
      items.push(JSON.parse(row.claim_json));
    }
    stmtI.free();
    return { total, items, filters: { ...f, offset, limit } };
  }

  get(id: string): Claim | null {
    const stmt = this.db.prepare('SELECT claim_json FROM claims WHERE id = $id');
    stmt.bind({ $id: id });
    const exists = stmt.step();
    const item = exists ? (stmt.getAsObject() as { claim_json: string }).claim_json : null;
    stmt.free();
    return item ? (JSON.parse(item) as Claim) : null;
  }

  private buildWhere(f: Filters) {
    const conditions: string[] = [];
    const params: Record<string, unknown> = {};
    if (f.modality) {
      conditions.push('modality = $modality');
      params.$modality = f.modality;
    }
    if (f.jurisdiction) {
      conditions.push('jurisdiction = $jurisdiction');
      params.$jurisdiction = f.jurisdiction;
    }
    if (f.at) {
      conditions.push('effective_from <= $at');
      conditions.push('(effective_to IS NULL OR $at <= effective_to)');
      params.$at = f.at;
    }
    const sql = conditions.length ? 'WHERE ' + conditions.join(' AND ') : '';
    return { sql, params };
  }
}
