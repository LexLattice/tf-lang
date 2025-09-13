import { describe, it, expect } from 'vitest';
import { makeHandler, makeRawHandler, createHost } from '../src/server.js';
import { canonicalJsonBytes, blake3hex } from 'tf-lang-l0';
import { readFile } from 'node:fs/promises';

const td = new TextDecoder();

interface JournalEntry { canon: string; proof?: string }
interface Resp { world: unknown; delta: unknown; journal: JournalEntry[] }

describe('host-lite', () => {
  it('idempotent plan and apply', async () => {
    const host = createHost();
    const handler = makeHandler(host);
    const body = { world: 'w', plan: 1 };
    const p1 = await handler('POST', '/plan', body);
    const p2 = await handler('POST', '/plan', body);
    expect(p1.status).toBe(200);
    expect(p2.status).toBe(200);
    const p1Bytes = td.decode(canonicalJsonBytes(p1.body));
    const p2Bytes = td.decode(canonicalJsonBytes(p2.body));
    expect(p1Bytes).toBe(p2Bytes);
    const a1 = await handler('POST', '/apply', body);
    const a2 = await handler('POST', '/apply', body);
    const a1Bytes = td.decode(canonicalJsonBytes(a1.body));
    const a2Bytes = td.decode(canonicalJsonBytes(a2.body));
    expect(a1Bytes).toBe(a2Bytes);
  });

  it('canonical journal and proof gating', async () => {
    const body = { world: 'c', plan: 2 };
    delete process.env.DEV_PROOFS;
    const h0 = makeHandler(createHost());
    const r0 = await h0('POST', '/apply', body);
    const j0 = (r0.body as Resp).journal[0];
    expect(j0.proof).toBeUndefined();
    const canon0 = td.decode(canonicalJsonBytes(JSON.parse(j0.canon)));
    expect(canon0).toBe(j0.canon);

    process.env.DEV_PROOFS = '1';
    const h1 = makeHandler(createHost());
    const r1 = await h1('POST', '/apply', body);
    const j1 = (r1.body as Resp).journal[0];
    const canon1 = td.decode(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(canon1).toBe(j1.canon);
    const hash = blake3hex(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(j1.proof).toBe(hash);
    delete process.env.DEV_PROOFS;
  });

  it('state is ephemeral', async () => {
    const h1 = makeHandler(createHost());
    await h1('POST', '/apply', { world: 'e', plan: 3 });
    const r1 = await h1('POST', '/plan', { world: 'e', plan: 0 });
    const w1 = (r1.body as Resp).world;

    const h2 = makeHandler(createHost());
    const r2 = await h2('POST', '/plan', { world: 'e', plan: 0 });
    const w2 = (r2.body as Resp).world;
    expect(w1).not.toEqual(w2);
  });

  it('404 for unknown path', async () => {
    const handler = makeHandler(createHost());
    const r = await handler('POST', '/nope', {});
    expect(r.status).toBe(404);
    const canon = td.decode(canonicalJsonBytes(r.body));
    expect(canon).toBe('{"error":"not_found"}');
  });

  it('404 for non-POST', async () => {
    const handler = makeHandler(createHost());
    const r = await handler('GET', '/plan', {});
    expect(r.status).toBe(404);
    const canon = td.decode(canonicalJsonBytes(r.body));
    expect(canon).toBe('{"error":"not_found"}');
  });

  it('400 for malformed json', async () => {
    const raw = makeRawHandler(createHost());
    const r = await raw('POST', '/plan', '{"world"');
    expect(r.status).toBe(400);
    const canon = td.decode(canonicalJsonBytes(r.body));
    expect(canon).toBe('{"error":"bad_request"}');
  });

  it('multi-world cache bounds', async () => {
    const host = createHost();
    const handler = makeHandler(host);
    const worlds = ['m0', 'm1', 'm2'];
    for (const w of worlds) {
      for (let i = 0; i < 40; i++) {
        await handler('POST', '/plan', { world: w, plan: i });
      }
    }
    for (const w of worlds) {
      const wc = host.cache.get(w);
      expect(wc?.size ?? 0).toBeLessThanOrEqual(32);
    }
  });

  it('no deep imports', async () => {
    const src = await readFile(new URL('../src/server.ts', import.meta.url), 'utf8');
    expect(src.includes('../')).toBe(false);
    expect(src.includes("from 'tf-lang-l0/")).toBe(false);
  });
});
