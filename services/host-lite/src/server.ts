import Fastify, { type FastifyInstance } from 'fastify';
import { canonicalJsonBytes, blake3hex } from '../../../packages/tf-lang-l0-ts/src/index.js';
import { DummyHost } from '../../../packages/tf-lang-l0-ts/src/host/memory.js';

const td = new TextDecoder();

interface PlanReq { world: string; plan: unknown }
interface JournalEntry { canon: string; proof?: string }

type Cache = Map<string, Map<string, string>>;

export function createServer(): FastifyInstance {
  const f = Fastify({ logger: false });
  const worlds = new Map<string, unknown>();
  const cache: Cache = new Map();

  f.post('/plan', async (req, reply) => {
    const body = req.body as PlanReq;
    const key = blake3hex(canonicalJsonBytes(body));
    const worldCache = cache.get(body.world);
    if (worldCache && worldCache.has('plan:' + key)) {
      return JSON.parse(worldCache.get('plan:' + key)!);
    }
    const w = worlds.get(body.world) ?? [];
    const delta = await DummyHost.call_tf('tf://plan/delta@0.1', [w, body.plan]);
    const world1 = await DummyHost.diff_apply(w, delta);
    const s0 = await DummyHost.snapshot_make(w);
    const id0 = await DummyHost.snapshot_id(s0);
    const s1 = await DummyHost.snapshot_make(world1);
    const id1 = await DummyHost.snapshot_id(s1);
    const entry = await DummyHost.journal_record(body.plan, delta, id0, id1, {});
    const canon = td.decode(canonicalJsonBytes(entry));
    const je: JournalEntry = { canon };
    if (process.env.DEV_PROOFS === '1') {
      je.proof = blake3hex(canonicalJsonBytes(entry));
    }
    const resp = { world: world1, delta, journal: [je] };
    const canonResp = td.decode(canonicalJsonBytes(resp));
    const respObj = JSON.parse(canonResp) as { world: unknown; delta: unknown; journal: JournalEntry[] };
    if (worldCache) {
      worldCache.set('plan:' + key, canonResp);
    } else {
      cache.set(body.world, new Map([[ 'plan:' + key, canonResp ]]));
    }
    return respObj;
  });

  f.post('/apply', async (req, reply) => {
    const body = req.body as PlanReq;
    const key = blake3hex(canonicalJsonBytes(body));
    let worldCache = cache.get(body.world);
    if (!worldCache) {
      worldCache = new Map();
      cache.set(body.world, worldCache);
    }
    const cached = worldCache.get('apply:' + key);
    if (cached) {
      return JSON.parse(cached);
    }
    const w = worlds.get(body.world) ?? [];
    const delta = await DummyHost.call_tf('tf://plan/delta@0.1', [w, body.plan]);
    const world1 = await DummyHost.diff_apply(w, delta);
    const s0 = await DummyHost.snapshot_make(w);
    const id0 = await DummyHost.snapshot_id(s0);
    const s1 = await DummyHost.snapshot_make(world1);
    const id1 = await DummyHost.snapshot_id(s1);
    const entry = await DummyHost.journal_record(body.plan, delta, id0, id1, {});
    const canon = td.decode(canonicalJsonBytes(entry));
    const je: JournalEntry = { canon };
    if (process.env.DEV_PROOFS === '1') {
      je.proof = blake3hex(canonicalJsonBytes(entry));
    }
    const resp = { world: world1, delta, journal: [je] };
    const canonResp = td.decode(canonicalJsonBytes(resp));
    const respObj = JSON.parse(canonResp) as { world: unknown; delta: unknown; journal: JournalEntry[] };
    worldCache.set('apply:' + key, canonResp);
    worlds.set(body.world, world1);
    return respObj;
  });

  return f;
}

if (process.argv[1] === new URL(import.meta.url).pathname) {
  const port = Number(process.env.PORT || 8787);
  const host = process.env.HOST || '0.0.0.0';
  createServer().listen({ port, host }).then(() => {
    console.log(`[host-lite] listening on http://${host}:${port}`);
  });
}
