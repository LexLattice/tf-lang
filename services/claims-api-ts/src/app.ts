import Fastify from 'fastify';
import { openDb, count as qCount, list as qList, getClaim } from './db.js';
import { parseFilters } from './filters.js';

export function buildApp() {
  const DB = openDb();
  const fastify = Fastify({ logger: false });

  fastify.addHook('onSend', async (_req, reply, payload) => {
    reply.header('Access-Control-Allow-Origin', '*');
    reply.header(
      'Access-Control-Allow-Headers',
      'Origin, X-Requested-With, Content-Type, Accept, Authorization'
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
      return reply.code(400).send({ error: 'bad_request' });
    }
  });

  fastify.get('/claims/list', async (req, reply) => {
    try {
      const f = parseFilters(req.query as Record<string, unknown>);
      return qList(DB, f);
    } catch {
      return reply.code(400).send({ error: 'bad_request' });
    }
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
    endpoints: ['/health', '/claims/count', '/claims/list', '/claims/explain/:id'],
    dataset_version: DB.datasetVersion,
  }));

  return fastify;
}
