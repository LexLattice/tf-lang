import Fastify from 'fastify';
import { openDb, count as qCount, list as qList, getClaim } from './db.js';
import type { ClaimDb } from './db.js';
import { parseFilters } from './filters.js';

export function buildApp() {
  let DB: ClaimDb | null = null;
  try {
    DB = openDb();
  } catch {
    DB = null;
  }
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

  fastify.get('/health', async (_req, reply) => {
    if (!DB) return reply.code(500).send({ error: 'db_unavailable' });
    return { ok: true, dataset_version: DB.datasetVersion };
  });

  fastify.get('/claims/count', async (req, reply) => {
    if (!DB) return reply.code(500).send({ error: 'db_unavailable' });
    try {
      const f = parseFilters(req.query as Record<string, unknown>);
      return qCount(DB, f);
    } catch {
      return reply.code(400).send({ error: 'bad_request' });
    }
  });

  fastify.get('/claims/list', async (req, reply) => {
    if (!DB) return reply.code(500).send({ error: 'db_unavailable' });
    try {
      const f = parseFilters(req.query as Record<string, unknown>);
      return qList(DB, f);
    } catch {
      return reply.code(400).send({ error: 'bad_request' });
    }
  });

  fastify.get('/claims/explain/:id', async (req, reply) => {
    if (!DB) return reply.code(500).send({ error: 'db_unavailable' });
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

  fastify.get('/', async (_req, reply) => {
    if (!DB) return reply.code(500).send({ error: 'db_unavailable' });
    return {
      service: 'claims-api-ts',
      endpoints: ['/health', '/claims/count', '/claims/list', '/claims/explain/:id'],
      dataset_version: DB.datasetVersion,
    };
  });

  return fastify;
}
