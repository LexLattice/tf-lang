import { canonicalJsonBytes, blake3hex, DummyHost } from 'tf-lang-l0';
import { createServer as createHttpServer } from 'node:http';

const td = new TextDecoder();

interface HostLite {
  handle(req: Request): Promise<Response>;
  stats(): { worlds: number; applies: number };
}

export function createHost(): HostLite {
  type ApplyCache = { key: string; resp: string };
  const worlds = new Map<string, { world: unknown; apply?: ApplyCache }>();

  async function handle(req: Request): Promise<Response> {
    const url = new URL(req.url);
    if (req.method !== 'POST') return notFound();
    const body = (await req.json()) as { world: string; plan: unknown };
    if (url.pathname === '/plan') return plan(body);
    if (url.pathname === '/apply') return apply(body);
    return notFound();
  }

  async function plan(body: { world: string; plan: unknown }): Promise<Response> {
    const w = worlds.get(body.world)?.world ?? [];
    const delta = await DummyHost.call_tf('tf://plan/delta@0.1', [w, body.plan]);
    const world1 = await DummyHost.diff_apply(w, delta);
    const s0 = await DummyHost.snapshot_make(w);
    const id0 = await DummyHost.snapshot_id(s0);
    const s1 = await DummyHost.snapshot_make(world1);
    const id1 = await DummyHost.snapshot_id(s1);
    const entry = await DummyHost.journal_record(body.plan, delta, id0, id1, {});
    const entryBytes = canonicalJsonBytes(entry);
    const canon = td.decode(entryBytes);
    const je: { canon: string; proof?: string } = { canon };
    if (process.env.DEV_PROOFS === '1') {
      je.proof = blake3hex(entryBytes);
    }
    const resp = { world: world1, delta, journal: [je] };
    const respStr = td.decode(canonicalJsonBytes(resp));
    return json(respStr);
  }

  async function apply(body: { world: string; plan: unknown }): Promise<Response> {
    const key = blake3hex(canonicalJsonBytes(body));
    const entry = worlds.get(body.world);
    if (entry?.apply && entry.apply.key === key) {
      return json(entry.apply.resp);
    }
    const w = entry?.world ?? [];
    const delta = await DummyHost.call_tf('tf://plan/delta@0.1', [w, body.plan]);
    const world1 = await DummyHost.diff_apply(w, delta);
    const s0 = await DummyHost.snapshot_make(w);
    const id0 = await DummyHost.snapshot_id(s0);
    const s1 = await DummyHost.snapshot_make(world1);
    const id1 = await DummyHost.snapshot_id(s1);
    const entryObj = await DummyHost.journal_record(body.plan, delta, id0, id1, {});
    const entryBytes = canonicalJsonBytes(entryObj);
    const canon = td.decode(entryBytes);
    const je: { canon: string; proof?: string } = { canon };
    if (process.env.DEV_PROOFS === '1') {
      je.proof = blake3hex(entryBytes);
    }
    const resp = { world: world1, delta, journal: [je] };
    const respStr = td.decode(canonicalJsonBytes(resp));
    worlds.set(body.world, { world: world1, apply: { key, resp: respStr } });
    return json(respStr);
  }

  function stats() {
    let applies = 0;
    worlds.forEach((w) => { if (w.apply) applies += 1; });
    return { worlds: worlds.size, applies };
  }

  function notFound(): Response {
    const payload = td.decode(canonicalJsonBytes({ error: 'not_found' }));
    return new Response(payload, { status: 404, headers: { 'content-type': 'application/json' } });
  }

  function json(str: string): Response {
    return new Response(str, { status: 200, headers: { 'content-type': 'application/json' } });
  }

  return { handle, stats };
}

if (process.argv[1] === new URL(import.meta.url).pathname) {
  const host = createHost();
  const server = createHttpServer(async (req, res) => {
    const chunks: Uint8Array[] = [];
    req.on('data', (c) => chunks.push(c));
    req.on('end', async () => {
      const body = Buffer.concat(chunks).toString();
      const request = new Request(`http://localhost${req.url}`, { method: req.method, body });
      const response = await host.handle(request);
      res.statusCode = response.status;
      response.headers.forEach((v, k) => res.setHeader(k, v));
      const text = await response.text();
      res.end(text);
    });
  });
  const port = Number(process.env.PORT || 8787);
  const h = process.env.HOST || '0.0.0.0';
  server.listen(port, h, () => {
    console.log(`[host-lite] listening on http://${h}:${port}`);
  });
}
