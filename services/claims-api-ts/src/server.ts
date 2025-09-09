
import Fastify from 'fastify';
import fs from 'node:fs';
import path from 'node:path';
import { count as qCount, list as qList, type Claim } from 'claims-core-ts';
import type { Filters } from './types.js';
import { queryHash } from './util.js';

const PORT = Number(process.env.PORT || 8787);
const HOST = process.env.HOST || '0.0.0.0';
const DATA_PATH = process.env.CLAIMS_DATA || path.join(process.cwd(), 'data', 'claims.json');

const fastify = Fastify({ logger: false });

// CORS: permissive for demo (consider tightening in production)
fastify.addHook('onSend', async (req, reply, payload) => {
  reply.header('Access-Control-Allow-Origin', '*');
  reply.header('Access-Control-Allow-Headers', 'Origin, X-Requested-With, Content-Type, Accept, Authorization');
  reply.header('Access-Control-Allow-Methods', 'GET, OPTIONS');
  return payload;
});
fastify.options('/*', async (_req, reply) => reply.code(200).send());


type Dataset = { dataset_version: string; claims: Claim[] };
let DATA: Dataset = { dataset_version: 'dev', claims: [] };

function loadDataset() {
  const raw = fs.readFileSync(DATA_PATH, 'utf-8');
  DATA = JSON.parse(raw);
}

function toWhere(f: Filters): any {
  const where: any = { };
  if (f.modality) where.modality = f.modality;
  if (f.jurisdiction) where.scope = { jurisdiction: f.jurisdiction };
  if (f.at) where.at = f.at;
  return where;
}

fastify.get('/health', async () => ({ ok: true, dataset_version: DATA.dataset_version }));

fastify.get('/claims/count', async (req, reply) => {
  const f: Filters = {
    modality: (req.query as any).modality,
    jurisdiction: (req.query as any).jurisdiction,
    at: (req.query as any).at,
  };
  const where = toWhere(f);
  const res = qCount(DATA.claims, where);
  return {
    dataset_version: DATA.dataset_version,
    query_hash: queryHash(f),
    filters: f,
    n: res.n,
    samples: res.samples,
  };
});

fastify.get('/claims/list', async (req, reply) => {
  const f: Filters = {
    modality: (req.query as any).modality,
    jurisdiction: (req.query as any).jurisdiction,
    at: (req.query as any).at,
    limit: (req.query as any).limit ? Number((req.query as any).limit) : 50,
    offset: (req.query as any).offset ? Number((req.query as any).offset) : 0,
  };
  const where = toWhere(f);
  const res = qList(DATA.claims, where).items;
  const items = res.slice(f.offset, f.offset + f.limit);
  return {
    dataset_version: DATA.dataset_version,
    query_hash: queryHash(f),
    filters: f,
    total: res.length,
    items,
  };
});

fastify.get('/claims/explain/:id', async (req, reply) => {
  const { id } = req.params as any;
  const item = DATA.claims.find(c => c.id === id);
  if (!item) return reply.code(404).send({ error: 'not_found' });
  return {
    dataset_version: DATA.dataset_version,
    claim: item,
    evidence: item.evidence,
    explanation: item.explanation ?? null,
  };
});

fastify.get('/', async () => ({
  service: 'claims-api-ts',
  endpoints: ['/health','/claims/count','/claims/list','/claims/explain/:id'],
  dataset_version: DATA.dataset_version,
  data_path: DATA_PATH,
}));

loadDataset();

fastify.listen({ port: PORT, host: HOST }).then(() => {
  console.log(`[claims-api] listening on http://${HOST}:${PORT} using ${DATA_PATH}`);
});
