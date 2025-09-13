import { describe, it, expect } from 'vitest';
import { makeHandler, createHost } from '../src/server.js';
import { canonicalJsonBytes, blake3hex } from 'tf-lang-l0';
import { readFile, readdir } from 'node:fs/promises';
import { join } from 'node:path';

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
    expect(p1.body).toEqual(p2.body);
    const a1 = await handler('POST', '/apply', body);
    const a2 = await handler('POST', '/apply', body);
    expect(a1.body).toEqual(a2.body);
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

  it('400 for malformed JSON', async () => {
    const handler = makeHandler(createHost());
    const r = await handler('POST', '/plan');
    expect(r.status).toBe(400);
    const canon = td.decode(canonicalJsonBytes(r.body));
    expect(canon).toBe('{"error":"bad_request"}');
  });

  it('multi-world cache bounds', async () => {
    const host = createHost();
    const handler = makeHandler(host);
    const worlds = ['a', 'b', 'c'];
    for (const w of worlds) {
      for (let i = 0; i < 40; i++) {
        await handler('POST', '/plan', { world: w, plan: i });
      }
    }
    for (const w of worlds) {
      const worldCache = host.cache.get(w);
      expect(worldCache?.size ?? 0).toBeLessThanOrEqual(32);
    }
    expect(host.cache.size).toBe(worlds.length);
  });

  it('package.json exports main', async () => {
    const pkg = JSON.parse(await readFile(new URL('../package.json', import.meta.url), 'utf8'));
    expect(pkg.main).toBe('src/server.ts');
    expect(pkg.exports).toBe('./src/server.ts');
  });

  it('no deep imports', async () => {
    async function* walk(dir: string): AsyncGenerator<string> {
      for (const entry of await readdir(dir, { withFileTypes: true })) {
        const full = join(dir, entry.name);
        if (entry.isDirectory()) {
          yield* walk(full);
        } else if (entry.isFile() && full.endsWith('.ts')) {
          yield full;
        }
      }
    }
    const root = new URL('../src', import.meta.url);
    for await (const file of walk(root.pathname)) {
      const src = await readFile(file, 'utf8');
      expect(src.includes('../')).toBe(false);
    }
  });
});
