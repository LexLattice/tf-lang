import { createServer as createHttpServer } from 'node:http';
import { canonicalJsonBytes, blake3hex, DummyHost } from 'tf-lang-l0';
import { makeHandler, type LruCache } from './handler.js';
import { makeRawHandler } from './makeRawHandler.js';

type PlanReq = { world: string; plan: unknown };
type JournalEntry = { canon: string; proof?: string };

export function createHost(): { exec: (world: string, plan: unknown) => Promise<{ world: unknown; delta: unknown; journal: JournalEntry[] }>; lru: LruCache; cache: LruCache } {
  const worlds = new Map<string, unknown>();
  const lru: LruCache = new Map();
  const td = new TextDecoder();

  async function exec(world: string, plan: unknown): Promise<{ world: unknown; delta: unknown; journal: JournalEntry[] }> {
    const w = worlds.get(world) ?? [];
    const delta = await DummyHost.call_tf('tf://plan/delta@0.1', [w, plan]);
    const world1 = await DummyHost.diff_apply(w, delta);
    const s0 = await DummyHost.snapshot_make(w);
    const id0 = await DummyHost.snapshot_id(s0);
    const s1 = await DummyHost.snapshot_make(world1);
    const id1 = await DummyHost.snapshot_id(s1);
    const entry = await DummyHost.journal_record(plan, delta, id0, id1, {});
    const entryBytes = canonicalJsonBytes(entry);
    const je: JournalEntry = { canon: td.decode(entryBytes) };
    if (process.env.DEV_PROOFS === '1') {
      je.proof = blake3hex(entryBytes);
    }
    return { world: world1, delta, journal: [je] };
  }

  return { exec, lru, cache: lru };
}

export function createServer(deps = createHost()) {
  const handler = makeHandler(deps);
  const rawHandler = makeRawHandler({ makeHandler: handler });
  return createHttpServer((req, res) => {
    const chunks: Uint8Array[] = [];
    req.on('data', (c) => chunks.push(c));
    req.on('end', async () => {
      const bodyStr = Buffer.concat(chunks).toString();
      const { status, body } = await rawHandler(
        req.method ?? '',
        req.url ?? '',
        bodyStr,
      );
      res.statusCode = status;
      res.setHeader('content-type', 'application/json');
      const bytes = canonicalJsonBytes(body);
      res.end(Buffer.from(bytes));
    });
  });
}

export { makeHandler } from './handler.js';
export { makeRawHandler } from './makeRawHandler.js';

if (process.argv[1] === new URL(import.meta.url).pathname) {
  const port = Number(process.env.PORT || 8787);
  const host = process.env.HOST || '0.0.0.0';
  createServer().listen(port, host, () => {
    console.log(`[host-lite] listening on http://${host}:${port}`);
  });
}
