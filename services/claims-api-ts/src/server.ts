import Fastify from 'fastify';
import path from 'node:path';
import { open, count as dbCount, list as dbList, getById, type Filters } from 'adapter-legal-ts';
import { queryHash } from './util.js';

const PORT = Number(process.env.PORT || 8787);
const HOST = process.env.HOST || '0.0.0.0';
const DB_PATH = process.env.CLAIMS_DB || path.join(process.cwd(), 'data', 'claims.db');

export function buildServer(dbPath = DB_PATH) {
  const db = open(dbPath);
  const fastify = Fastify({ logger: false });

  fastify.addHook('onSend', async (_req, reply, payload) => {
    reply.header('Access-Control-Allow-Origin', '*');
    reply.header('Access-Control-Allow-Headers', 'Origin, X-Requested-With, Content-Type, Accept, Authorization');
    reply.header('Access-Control-Allow-Methods', 'GET, OPTIONS');
    return payload;
  });
  fastify.options('/*', async (_req, reply) => reply.code(200).send());

  fastify.get('/health', async () => ({ ok: true, dataset_version: db.datasetVersion }));

  fastify.get('/claims/count', async (req) => {
    const f: Filters = {
      modality: (req.query as any).modality,
      jurisdiction: (req.query as any).jurisdiction,
      at: (req.query as any).at,
    };
    const res = dbCount(db, f);
    return {
      dataset_version: db.datasetVersion,
      query_hash: queryHash(f),
      filters: f,
      n: res.n,
      samples: res.samples,
    };
  });

  fastify.get('/claims/list', async (req) => {
    const f: Filters & { limit?: number; offset?: number } = {
      modality: (req.query as any).modality,
      jurisdiction: (req.query as any).jurisdiction,
      at: (req.query as any).at,
      limit: (req.query as any).limit,
      offset: (req.query as any).offset,
    };
    const rows = dbList(db, f).items;
    const rawOffset = Number(f.offset);
    const offset = Number.isFinite(rawOffset) ? Math.max(0, rawOffset) : 0;
    const rawLimit = Number(f.limit);
    const limit0 = Number.isFinite(rawLimit) ? rawLimit : 10;
    const limit = Math.min(Math.max(1, limit0), 200);
    const items = rows.slice(offset, offset + limit);

    const responseFilters: Filters & { offset: number; limit: number } = {
      modality: f.modality,
      jurisdiction: f.jurisdiction,
      at: f.at,
      offset,
      limit,
    };

    return {
      dataset_version: db.datasetVersion,
      query_hash: queryHash(responseFilters),
      filters: responseFilters,
      total: rows.length,
      items,
    };
  });

  fastify.get('/claims/explain/:id', async (req, reply) => {
    const { id } = req.params as any;
    const item = getById(db, id);
    if (!item) return reply.code(404).send({ error: 'not_found' });
    return {
      dataset_version: db.datasetVersion,
      claim: item,
      evidence: item.evidence,
      explanation: item.explanation ?? null,
    };
  });

  fastify.get('/', async () => ({
    service: 'claims-api-ts',
    endpoints: ['/health', '/claims/count', '/claims/list', '/claims/explain/:id'],
    dataset_version: db.datasetVersion,
    db_path: dbPath,
  }));

  return fastify;
}

if (process.env.NODE_ENV !== 'test') {
  const app = buildServer();
  app.listen({ port: PORT, host: HOST }).then(() => {
    console.log(`[claims-api] listening on http://${HOST}:${PORT} using ${DB_PATH}`);
  });
}
