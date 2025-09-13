import Fastify from 'fastify';
import type { Filters } from './types.js';
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

fastify.get('/claims/count', async (req) => {
  const q = req.query as Record<string, string>;
  const f: Filters = { modality: q.modality, jurisdiction: q.jurisdiction, at: q.at };
  return qCount(DB, f);
});

fastify.get('/claims/list', async (req) => {
  const q = req.query as Record<string, string>;
  const f: Filters = {
    modality: q.modality,
    jurisdiction: q.jurisdiction,
    at: q.at,
    limit: q.limit ? Number(q.limit) : undefined,
    offset: q.offset ? Number(q.offset) : undefined,
  };
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
