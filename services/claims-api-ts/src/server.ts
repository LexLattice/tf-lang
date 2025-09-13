
import Fastify from 'fastify';
import path from 'node:path';
import { ClaimsDB } from './db.js';
import type { Filters } from './types.js';
import { queryHash } from './util.js';

const PORT = Number(process.env.PORT || 8787);
const HOST = process.env.HOST || '0.0.0.0';
const DB_PATH = process.env.CLAIMS_DB || path.join(process.cwd(), 'data', 'claims.db');

const fastify = Fastify({ logger: false });

// CORS: permissive for demo (consider tightening in production)
fastify.addHook('onSend', async (req, reply, payload) => {
  reply.header('Access-Control-Allow-Origin', '*');
  reply.header('Access-Control-Allow-Headers', 'Origin, X-Requested-With, Content-Type, Accept, Authorization');
  reply.header('Access-Control-Allow-Methods', 'GET, OPTIONS');
  return payload;
});
fastify.options('/*', async (_req, reply) => reply.code(200).send());


let DB: ClaimsDB;

function toWhere(f: Filters): any {
  const where: any = { };
  if (f.modality) where.modality = f.modality;
  if (f.jurisdiction) where.scope = { jurisdiction: f.jurisdiction };
  if (f.at) where.at = f.at;
  return where;
}

fastify.get('/health', async () => ({ ok: true, dataset_version: DB.datasetVersion }));

fastify.get('/claims/count', async (req, reply) => {
  const q: any = req.query;
  const f: Filters = {
    modality: q.modality,
    jurisdiction: q.jurisdiction,
    at: q.at,
  };
  const where = toWhere(f);
  const res = DB.count(where);
  return {
    dataset_version: DB.datasetVersion,
    query_hash: queryHash(f),
    filters: f,
    n: res.n,
    samples: res.samples,
  };
});

fastify.get('/claims/list', async (req, reply) => {
  const q: any = req.query;
  const f: Filters = {
    modality: q.modality,
    jurisdiction: q.jurisdiction,
    at: q.at,
    limit: q.limit,
    offset: q.offset,
  };
  const res = DB.list(f);
  return {
    dataset_version: DB.datasetVersion,
    query_hash: queryHash(res.filters),
    filters: res.filters,
    total: res.total,
    items: res.items,
  };
});

fastify.get('/claims/explain/:id', async (req, reply) => {
  const p: any = req.params;
  const { id } = p;
  const item = DB.get(id);
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
  data_path: DB_PATH,
}));

ClaimsDB.open(DB_PATH).then((db) => {
  DB = db;
  fastify.listen({ port: PORT, host: HOST }).then(() => {
    console.log(`[claims-api] listening on http://${HOST}:${PORT} using ${DB_PATH}`);
  });
});
