import Fastify from 'fastify';
import type { Filters, Modality } from './types.js';
import { openDb, count as qCount, list as qList, getClaim } from './db.js';

const PORT = Number(process.env.PORT || 8787);
const HOST = process.env.HOST || '0.0.0.0';
const DB = openDb();

export const fastify = Fastify({ logger: false });

// CORS: permissive for demo (consider tightening in production)
fastify.addHook('onSend', async (_req, reply, payload) => {
  reply.header('Access-Control-Allow-Origin', '*');
  reply.header('Access-Control-Allow-Headers', 'Origin, X-Requested-With, Content-Type, Accept, Authorization');
  reply.header('Access-Control-Allow-Methods', 'GET, OPTIONS');
  return payload;
});
fastify.options('/*', async (_req, reply) => reply.code(200).send());

fastify.get('/health', async () => ({ ok: true, dataset_version: DB.datasetVersion }));

function parseFilters(q: Record<string, string>): Filters {
  const f: Filters = {};
  if (q.modality !== undefined) {
    const mods: Modality[] = ['FORBIDDEN', 'PERMITTED', 'OBLIGATORY', 'EXEMPT', 'EXCEPTION'];
    if (!mods.includes(q.modality as Modality)) throw new Error('bad modality');
    f.modality = q.modality as Modality;
  }
  if (q.jurisdiction !== undefined) {
    if (!/^[A-Za-z]{2}$/.test(q.jurisdiction)) throw new Error('bad jurisdiction');
    f.jurisdiction = q.jurisdiction;
  }
  if (q.at !== undefined) {
    if (!/^\d{4}-\d{2}-\d{2}$/.test(q.at)) throw new Error('bad at');
    f.at = q.at;
  }
  if (q.limit !== undefined) {
    const lim = Number(q.limit);
    if (!Number.isFinite(lim)) throw new Error('bad limit');
    f.limit = lim;
  }
  if (q.offset !== undefined) {
    const off = Number(q.offset);
    if (!Number.isFinite(off)) throw new Error('bad offset');
    f.offset = off;
  }
  return f;
}

fastify.get('/claims/count', async (req, reply) => {
  try {
    const f = parseFilters(req.query as Record<string, string>);
    return qCount(DB, f);
  } catch {
    return reply.code(400).send({ error: 'bad_request' });
  }
});

fastify.get('/claims/list', async (req, reply) => {
  try {
    const f = parseFilters(req.query as Record<string, string>);
    return qList(DB, f);
  } catch {
    return reply.code(400).send({ error: 'bad_request' });
  }
});

fastify.get('/claims/explain/:id', async (req, reply) => {
  const { id } = req.params as Record<string, string>;
  if (!/^[A-Za-z0-9_-]+$/.test(id)) return reply.code(400).send({ error: 'bad_request' });
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

if (process.env.NODE_ENV !== 'test') {
  fastify.listen({ port: PORT, host: HOST }).then(() => {
    console.log(`[claims-api] listening on http://${HOST}:${PORT}`);
  });
}

export default fastify;
