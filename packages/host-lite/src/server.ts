import http, { type IncomingMessage, type ServerResponse } from 'node:http';
import { canonicalJsonBytes, blake3hex, DummyHost } from 'tf-lang-l0';

const td = new TextDecoder();
const MAX_CACHE = 16;

interface PlanReq { world: string; plan: unknown }
interface JournalEntry { canon: string; proof?: string }
interface HandlerResp { status: number; body: string }

export function createHostLite() {
  const worlds = new Map<string, unknown>();
  const cache = new Map<string, Map<string, string>>();

  async function handle(method: string, url: string, body: PlanReq): Promise<HandlerResp> {
    if (method !== 'POST' || (url !== '/plan' && url !== '/apply')) {
      const body = td.decode(canonicalJsonBytes({ error: 'not_found' }));
      return { status: 404, body };
    }
    const key = blake3hex(canonicalJsonBytes(body));
    let worldCache = cache.get(body.world);
    if (!worldCache) {
      worldCache = new Map();
      cache.set(body.world, worldCache);
    }
    const prefix = url === '/plan' ? 'plan:' : 'apply:';
    const cached = worldCache.get(prefix + key);
    if (cached) {
      return { status: 200, body: cached };
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
    const respObj = { world: world1, delta, journal: [je] };
    const canonResp = td.decode(canonicalJsonBytes(respObj));
    worldCache.set(prefix + key, canonResp);
    if (worldCache.size > MAX_CACHE) {
      const first = worldCache.keys().next().value as string | undefined;
      if (first) worldCache.delete(first);
    }
    if (url === '/apply') {
      worlds.set(body.world, world1);
    }
    return { status: 200, body: canonResp };
  }

  return {
    handle,
    cacheSize(world: string) {
      return cache.get(world)?.size ?? 0;
    },
  };
}

export function createServer() {
  const host = createHostLite();
  const srv = http.createServer(async (req: IncomingMessage, res: ServerResponse) => {
    const chunks: Buffer[] = [];
    req.on('data', (c) => chunks.push(c as Buffer));
    req.on('end', async () => {
      const body = chunks.length ? JSON.parse(Buffer.concat(chunks).toString()) : {};
      const { status, body: resp } = await host.handle(req.method || '', req.url || '', body);
      res.statusCode = status;
      res.setHeader('content-type', 'application/json');
      res.end(resp);
    });
  });
  return srv;
}

if (process.argv[1] === new URL(import.meta.url).pathname) {
  const port = Number(process.env.PORT || 8787);
  const host = process.env.HOST || '0.0.0.0';
  createServer().listen(port, host, () => {
    console.log(`[host-lite] listening on http://${host}:${port}`);
  });
}
