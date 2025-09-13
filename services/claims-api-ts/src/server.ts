import Fastify from 'fastify';
import { openDb, count as qCount, list as qList, getClaim } from './db.js';
import type { Filters, Modality } from './types.js';

const MODALITIES: Modality[] = ['FORBIDDEN', 'PERMITTED', 'OBLIGATORY', 'EXEMPT', 'EXCEPTION'];

function parseFilters(q: Record<string, unknown>): Filters {
  const f: Filters = {};
  if (q.modality !== undefined) {
    if (typeof q.modality !== 'string' || !MODALITIES.includes(q.modality as Modality)) {
      throw new Error('modality');
    }
    f.modality = q.modality as Modality;
  }
  if (q.jurisdiction !== undefined) {
    if (typeof q.jurisdiction !== 'string') throw new Error('jurisdiction');
    f.jurisdiction = q.jurisdiction;
  }
  if (q.at !== undefined) {
    if (typeof q.at !== 'string') throw new Error('at');
    f.at = q.at;
  }
  if (q.limit !== undefined) {
    const n = Number(q.limit);
    if (!Number.isFinite(n)) throw new Error('limit');
    f.limit = n;
  }
  if (q.offset !== undefined) {
    const n = Number(q.offset);
    if (!Number.isFinite(n)) throw new Error('offset');
    f.offset = n;
  }
  return f;
}

export function buildServer() {
  const DB = openDb();
  const fastify = Fastify({ logger: false });

  fastify.addHook('onSend', async (_req, reply, payload) => {
    reply.header('Access-Control-Allow-Origin', '*');
    reply.header(
      'Access-Control-Allow-Headers',
      'Origin, X-Requested-With, Content-Type, Accept, Authorization',
    );
    reply.header('Access-Control-Allow-Methods', 'GET, OPTIONS');
    return payload;
  });
  fastify.options('/*', async (_req, reply) => reply.code(200).send());

  fastify.get('/health', async () => ({ ok: true, dataset_version: DB.datasetVersion }));

  fastify.get('/claims/count', async (req, reply) => {
    try {
      const f = parseFilters(req.query as Record<string, unknown>);
      return qCount(DB, f);
    } catch {
      return reply.code(400).send({ error: 'invalid_query' });
    }
  });

  fastify.get('/claims/list', async (req, reply) => {
    try {
      const f = parseFilters(req.query as Record<string, unknown>);
      return qList(DB, f);
    } catch {
      return reply.code(400).send({ error: 'invalid_query' });
    }
  });

  fastify.get('/claims/explain/:id', async (req, reply) => {
    const { id } = req.params as Record<string, unknown>;
    if (typeof id !== 'string' || !id) {
      return reply.code(400).send({ error: 'invalid_id' });
    }
    const item = getClaim(DB, id);
    if (!item) return reply.code(404).send({ error: 'not_found' });
    return {
      dataset_version: DB.datasetVersion,
      claim: item,
      evidence: item.evidence,
      explanation: item.explanation ?? null,
    };
  });

  fastify.get('/', async () => ({
    service: 'claims-api-ts',
    endpoints: [
      '/health',
      '/claims/count',
      '/claims/list',
      '/claims/explain/:id',
    ],
    dataset_version: DB.datasetVersion,
  }));

  return fastify;
}

const PORT = Number(process.env.PORT || 8787);
const HOST = process.env.HOST || '0.0.0.0';
if (import.meta.url === new URL(process.argv[1], 'file://').href) {
  buildServer().listen({ port: PORT, host: HOST }).then(() => {
    console.log(`[claims-api] listening on http://${HOST}:${PORT}`);
  });
}

