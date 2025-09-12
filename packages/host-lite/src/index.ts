import { canonicalJsonBytes, blake3hex, DummyHost } from 'tf-lang-l0';
import { createServer as createHttpServer, IncomingMessage, ServerResponse } from 'node:http';

const td = new TextDecoder();

interface PlanReq { world: string; plan: unknown }
interface JournalEntry { canon: string; proof?: string }
interface RespBody { world: unknown; delta: unknown; journal: JournalEntry[] }

type Cache = Map<string, Map<string, string>>;

const WORLD_LIMIT = 16;
const CACHE_LIMIT = 16;

function setWithLimit<K, V>(map: Map<K, V>, key: K, value: V, limit: number) {
  if (!map.has(key) && map.size >= limit) {
    const firstKey = map.keys().next().value;
    map.delete(firstKey);
  }
  map.set(key, value);
}

export function createHost() {
  const worlds = new Map<string, unknown>();
  const cache: Cache = new Map();

  async function handle(method: string, path: string, body: unknown): Promise<{ status: number; body: string }> {
    if (method !== 'POST' || (path !== '/plan' && path !== '/apply')) {
      const err = td.decode(canonicalJsonBytes({ error: 'not found' }));
      return { status: 404, body: err };
    }
    const b = body as PlanReq;
    const key = blake3hex(canonicalJsonBytes(b));
    let worldCache = cache.get(b.world);
    if (!worldCache) {
      worldCache = new Map();
      setWithLimit(cache, b.world, worldCache, WORLD_LIMIT);
    }
    const cacheKey = `${path.slice(1)}:${key}`;
    const cached = worldCache.get(cacheKey);
    if (cached) {
      return { status: 200, body: cached };
    }
    const w = worlds.get(b.world) ?? [];
    const delta = await DummyHost.call_tf('tf://plan/delta@0.1', [w, b.plan]);
    const world1 = await DummyHost.diff_apply(w, delta);
    const s0 = await DummyHost.snapshot_make(w);
    const id0 = await DummyHost.snapshot_id(s0);
    const s1 = await DummyHost.snapshot_make(world1);
    const id1 = await DummyHost.snapshot_id(s1);
    const entry = await DummyHost.journal_record(b.plan, delta, id0, id1, {});
    const canonBytes = canonicalJsonBytes(entry);
    const canon = td.decode(canonBytes);
    const je: JournalEntry = { canon };
    if (process.env.DEV_PROOFS === '1') {
      je.proof = blake3hex(canonBytes);
    }
    const resp: RespBody = { world: world1, delta, journal: [je] };
    const canonResp = td.decode(canonicalJsonBytes(resp));
    setWithLimit(worldCache, cacheKey, canonResp, CACHE_LIMIT);
    if (path === '/apply') {
      setWithLimit(worlds, b.world, world1, WORLD_LIMIT);
    }
    return { status: 200, body: canonResp };
  }

  function stats() {
    let entries = 0;
    for (const m of cache.values()) entries += m.size;
    return { worlds: worlds.size, entries };
  }

  async function request(opts: { method: string; path: string; body?: unknown }) {
    const res = await handle(opts.method, opts.path, opts.body);
    return { statusCode: res.status, body: res.body };
  }

  function listener(req: IncomingMessage, res: ServerResponse) {
    const chunks: Uint8Array[] = [];
    req.on('data', (c) => chunks.push(c));
    req.on('end', async () => {
      const bodyStr = Buffer.concat(chunks).toString('utf8') || '{}';
      let obj: unknown;
      try {
        obj = JSON.parse(bodyStr);
      } catch {
        obj = {};
      }
      const result = await handle(req.method ?? '', req.url ?? '', obj);
      res.statusCode = result.status;
      res.setHeader('content-type', 'application/json');
      res.end(result.body);
    });
  }

  return { request, listener, stats };
}

if (process.argv[1] === new URL(import.meta.url).pathname) {
  const port = Number(process.env.PORT || 8787);
  const host = process.env.HOST || '0.0.0.0';
  const { listener } = createHost();
  createHttpServer(listener).listen(port, host, () => {
    console.log(`[host-lite] listening on http://${host}:${port}`);
  });
}
