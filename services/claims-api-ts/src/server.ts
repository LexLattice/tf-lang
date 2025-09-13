import Fastify from 'fastify';
import fs from 'node:fs';
import path from 'node:path';
import initSqlJs from 'sql.js';
import type { Claim } from 'claims-core-ts';
import type { Filters } from './types.js';
import { queryHash } from './util.js';

const PORT = Number(process.env.PORT || 8787);
const HOST = process.env.HOST || '0.0.0.0';

export async function buildServer(dbPath = process.env.CLAIMS_DB || path.join(process.cwd(), 'data', 'claims.db')) {
  const SQL = await initSqlJs();
  const file = fs.readFileSync(dbPath);
  const db = new SQL.Database(file);
  const versionRes = db.exec("SELECT value FROM meta WHERE key='dataset_version'");
  const datasetVersion = versionRes[0]?.values[0][0] as string | undefined || 'dev';

  const fastify = Fastify({ logger: false });

  fastify.addHook('onSend', async (_req, reply, payload) => {
    reply.header('Access-Control-Allow-Origin', '*');
    reply.header('Access-Control-Allow-Headers', 'Origin, X-Requested-With, Content-Type, Accept, Authorization');
    reply.header('Access-Control-Allow-Methods', 'GET, OPTIONS');
    return payload;
  });
  fastify.options('/*', async (_req, reply) => reply.code(200).send());

  function whereSql(f: Filters): { sql: string; params: unknown[] } {
    const parts: string[] = [];
    const params: unknown[] = [];
    if (f.modality) { parts.push('modality = ?'); params.push(f.modality); }
    if (f.jurisdiction) { parts.push('jurisdiction = ?'); params.push(f.jurisdiction); }
    if (f.at) { parts.push('effective_from <= ? AND (? <= effective_to OR effective_to IS NULL)'); params.push(f.at, f.at); }
    const sql = parts.length ? 'WHERE ' + parts.join(' AND ') : '';
    return { sql, params };
  }

  function all(sql: string, params: unknown[]): Record<string, unknown>[] {
    const stmt = db.prepare(sql);
    stmt.bind(params);
    const rows: Record<string, unknown>[] = [];
    while (stmt.step()) rows.push(stmt.getAsObject());
    stmt.free();
    return rows;
  }

  function rowToClaim(r: Record<string, unknown>): Claim {
    return {
      id: String(r.id),
      kind: 'DEONTIC',
      modality: r.modality as Claim['modality'],
      scope: { jurisdiction: r.jurisdiction as string | undefined },
      effective: { from: r.effective_from as string, to: (r.effective_to as string | null) ?? null },
      status: (r.status as Claim['status']) ?? 'determinate',
      explanation: undefined,
      evidence: [{
        source_uri: r.source_uri as string,
        span: null,
        hash: String(Math.abs(hashCode(String(r.text ?? '')))),
        rule_id: 'db.v1',
      }],
      dataset_version: datasetVersion,
      query_hash: '0',
    };
  }

  fastify.get('/health', async () => ({ ok: true, dataset_version: datasetVersion }));

  fastify.get('/claims/count', async (req) => {
    const q = req.query as Record<string, string>;
    const f: Filters = {
      modality: q.modality as Filters['modality'],
      jurisdiction: q.jurisdiction,
      at: q.at,
    };
    const w = whereSql(f);
    const rows = all(`SELECT id FROM claims ${w.sql} ORDER BY id`, w.params);
    const samples = rows.slice(0, 10).map(r => String(r.id));
    return {
      dataset_version: datasetVersion,
      query_hash: queryHash(f),
      filters: f,
      n: rows.length,
      samples,
    };
  });

  fastify.get('/claims/list', async (req) => {
    const q = req.query as Record<string, string>;
    const f: Filters = {
      modality: q.modality as Filters['modality'],
      jurisdiction: q.jurisdiction,
      at: q.at,
      limit: q.limit ? Number(q.limit) : undefined,
      offset: q.offset ? Number(q.offset) : undefined,
    };
    const w = whereSql(f);
    const rows = all(`SELECT * FROM claims ${w.sql} ORDER BY id`, w.params);
    const rawOffset = Number(f.offset);
    const offset = Number.isFinite(rawOffset) ? Math.max(0, rawOffset) : 0;
    const rawLimit = Number(f.limit);
    const limit0 = Number.isFinite(rawLimit) ? rawLimit : 10;
    const limit = Math.min(Math.max(1, limit0), 200);
    const items = rows.slice(offset, offset + limit).map(rowToClaim);
    const responseFilters: Filters = { modality: f.modality, jurisdiction: f.jurisdiction, at: f.at, offset, limit };
    return {
      dataset_version: datasetVersion,
      query_hash: queryHash(responseFilters),
      filters: responseFilters,
      total: rows.length,
      items,
    };
  });

  fastify.get('/claims/explain/:id', async (req, reply) => {
    const { id } = req.params as { id: string };
    const rows = all('SELECT * FROM claims WHERE id = ?', [id]);
    if (rows.length === 0) return reply.code(404).send({ error: 'not_found' });
    const claim = rowToClaim(rows[0]);
    return {
      dataset_version: datasetVersion,
      claim,
      evidence: claim.evidence,
      explanation: claim.explanation ?? null,
    };
  });

  fastify.get('/', async () => ({
    service: 'claims-api-ts',
    endpoints: ['/health', '/claims/count', '/claims/list', '/claims/explain/:id'],
    dataset_version: datasetVersion,
    db_path: dbPath,
  }));

  return fastify;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  buildServer().then(app => {
    app.listen({ port: PORT, host: HOST }).then(() => {
      console.log(`[claims-api] listening on http://${HOST}:${PORT} using ${process.env.CLAIMS_DB || path.join(process.cwd(), 'data', 'claims.db')}`);
    });
  });
}

function hashCode(s: string): number {
  let h = 0;
  for (let i = 0; i < s.length; i++) {
    h = (h << 5) - h + s.charCodeAt(i) | 0;
  }
  return h;
}
