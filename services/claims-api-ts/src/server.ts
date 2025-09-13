import Fastify from 'fastify';
import type { Filters, Modality } from './types.js';
import { openDb, count as qCount, list as qList, getClaim } from './db.js';

const PORT = Number(process.env.PORT || 8787);
const HOST = process.env.HOST || '0.0.0.0';
const DB = openDb();

const fastify = Fastify({ logger: false });

// CORS: permissive for demo (consider tightening in production)
fastify.addHook('onSend', async (_req, reply, payload) => {
  reply.header('Access-Control-Allow-Origin', '*');
  reply.header('Access-Control-Allow-Headers', 'Origin, X-Requested-With, Content-Type, Accept, Authorization');
  reply.header('Access-Control-Allow-Methods', 'GET, OPTIONS');
  return payload;
});
fastify.options('/*', async (_req, reply) => reply.code(200).send());

fastify.get('/health', async () => ({ ok: true, dataset_version: DB.datasetVersion }));

function parseFilters(q: Record<string, unknown>): Filters | null {
  const f: Filters = {};
  if (q.modality !== undefined) {
    const m = q.modality;
    if (m === 'FORBIDDEN' || m === 'PERMITTED' || m === 'OBLIGATORY' || m === 'EXEMPT' || m === 'EXCEPTION') {
      f.modality = m as Modality;
    } else return null;
  }
  if (q.jurisdiction !== undefined) {
    if (typeof q.jurisdiction === 'string') f.jurisdiction = q.jurisdiction;
    else return null;
  }
  if (q.at !== undefined) {
    if (typeof q.at === 'string' && /^\d{4}-\d{2}-\d{2}$/.test(q.at)) f.at = q.at;
    else return null;
  }
  if (q.limit !== undefined) {
    const n = Number(q.limit);
    if (Number.isFinite(n) && n >= 1 && n <= 200) f.limit = n;
    else return null;
  }
  if (q.offset !== undefined) {
    const n = Number(q.offset);
    if (Number.isFinite(n) && n >= 0) f.offset = n;
    else return null;
  }
  return f;
}

fastify.get('/claims/count', async (req, reply) => {
  const f = parseFilters(req.query as Record<string, unknown>);
  if (!f) return reply.code(400).send({ error: 'bad_request' });
  return qCount(DB, f);
});

fastify.get('/claims/list', async (req, reply) => {
  const f = parseFilters(req.query as Record<string, unknown>);
  if (!f) return reply.code(400).send({ error: 'bad_request' });
  return qList(DB, f);
});

fastify.get('/claims/explain/:id', async (req, reply) => {
  const { id } = req.params as Record<string, string>;
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
  endpoints: ['/health','/claims/count','/claims/list','/claims/explain/:id'],
  dataset_version: DB.datasetVersion,
}));

fastify.listen({ port: PORT, host: HOST }).then(() => {
  console.log(`[claims-api] listening on http://${HOST}:${PORT}`);
});
