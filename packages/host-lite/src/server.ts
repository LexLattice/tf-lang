import {
  createServer as createHttpServer,
  IncomingMessage,
  ServerResponse,
} from 'node:http';
import { canonicalJsonBytes, blake3hex, DummyHost } from 'tf-lang-l0';

const td = new TextDecoder();

interface PlanReq { world: string; plan: unknown }
interface JournalEntry { canon: string; proof?: string }

const MAX_CACHE = 32;

type Cache = Map<string, Map<string, string>>;

function cacheLookup(cache: Cache, world: string, key: string): string | undefined {
  const m = cache.get(world);
  if (!m) return undefined;
  const v = m.get(key);
  if (v !== undefined) {
    m.delete(key);
    m.set(key, v);
  }
  return v;
}

function cacheStore(cache: Cache, world: string, key: string, value: string) {
  let m = cache.get(world);
  if (!m) {
    m = new Map();
    cache.set(world, m);
  }
  if (m.has(key)) m.delete(key);
  m.set(key, value);
  if (m.size > MAX_CACHE) {
    const fk = m.keys().next().value as string;
    m.delete(fk);
  }
}

async function exec(
  worlds: Map<string, unknown>,
  cache: Cache,
  action: 'plan' | 'apply',
  body: PlanReq,
): Promise<{ world: unknown; delta: unknown; journal: JournalEntry[] }> {
  const key = action + ':' + blake3hex(canonicalJsonBytes(body));
  const cached = cacheLookup(cache, body.world, key);
  if (cached) return JSON.parse(cached);
  const w = worlds.get(body.world) ?? [];
  const delta = await DummyHost.call_tf('tf://plan/delta@0.1', [w, body.plan]);
  const world1 = await DummyHost.diff_apply(w, delta);
  const s0 = await DummyHost.snapshot_make(w);
  const id0 = await DummyHost.snapshot_id(s0);
  const s1 = await DummyHost.snapshot_make(world1);
  const id1 = await DummyHost.snapshot_id(s1);
  const entry = await DummyHost.journal_record(body.plan, delta, id0, id1, {});
  const entryBytes = canonicalJsonBytes(entry);
  const canon = td.decode(entryBytes);
  const je: JournalEntry = { canon };
  if (process.env.DEV_PROOFS === '1') {
    je.proof = blake3hex(entryBytes);
  }
  const resp = { world: world1, delta, journal: [je] };
  const respBytes = canonicalJsonBytes(resp);
  const canonResp = td.decode(respBytes);
  cacheStore(cache, body.world, key, canonResp);
  if (action === 'apply') worlds.set(body.world, world1);
  return JSON.parse(canonResp);
}

export function createHost() {
  const worlds = new Map<string, unknown>();
  const cache: Cache = new Map();

  return {
    cache,
    plan(body: PlanReq) {
      return exec(worlds, cache, 'plan', body);
    },
    apply(body: PlanReq) {
      return exec(worlds, cache, 'apply', body);
    },
  };
}

export function makeHandler(host = createHost()) {
  return async (method: string, url: string, body: unknown) => {
    if (method !== 'POST') return { status: 404, body: { error: 'not_found' } };
    if (url === '/plan') return { status: 200, body: await host.plan(body as PlanReq) };
    if (url === '/apply') return { status: 200, body: await host.apply(body as PlanReq) };
    return { status: 404, body: { error: 'not_found' } };
  };
}

export function makeRawHandler(host = createHost()) {
  const handler = makeHandler(host);
  return async (method: string, url: string, bodyStr: string) => {
    let body: unknown;
    try {
      body = JSON.parse(bodyStr || '{}');
    } catch {
      return { status: 400, body: { error: 'bad_request' } };
    }
    return handler(method, url, body);
  };
}

export function createNodeHandler(host = createHost()) {
  const raw = makeRawHandler(host);
  return async (req: IncomingMessage, res: ServerResponse) => {
    const chunks: Uint8Array[] = [];
    req.on('data', (c) => chunks.push(c));
    req.on('end', async () => {
      const bodyStr = Buffer.concat(chunks).toString();
      const { status, body } = await raw(
        req.method ?? '',
        req.url ?? '',
        bodyStr,
      );
      res.statusCode = status;
      res.setHeader('content-type', 'application/json');
      const bytes = canonicalJsonBytes(body);
      res.end(Buffer.from(bytes));
    });
  };
}

export function createServer(host = createHost()) {
  return createHttpServer(createNodeHandler(host));
}

if (process.argv[1] === new URL(import.meta.url).pathname) {
  const port = Number(process.env.PORT || 8787);
  const host = process.env.HOST || '0.0.0.0';
  createServer().listen(port, host, () => {
    console.log(`[host-lite] listening on http://${host}:${port}`);
  });
}
