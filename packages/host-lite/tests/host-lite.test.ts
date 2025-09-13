import { describe, it, expect } from 'vitest';
import { makeHandler, createHost, makeRawHandler } from '../src/server.js';
import { canonicalJsonBytes, blake3hex } from 'tf-lang-l0';

const td = new TextDecoder();

interface JournalEntry { canon: string; proof?: string }
interface Resp { world: unknown; delta: unknown; journal: JournalEntry[] }

describe('host-lite', () => {
  it('byte-identical determinism for plan/apply', async () => {
    const host = createHost();
    const raw = makeRawHandler(host);
    const bodyStr = JSON.stringify({ world: 'w', plan: 1 });
    const p1 = await raw('POST', '/plan', bodyStr);
    const p2 = await raw('POST', '/plan', bodyStr);
    expect(p1.status).toBe(200);
    expect(p2.status).toBe(200);
    const pb1 = td.decode(canonicalJsonBytes(p1.body));
    const pb2 = td.decode(canonicalJsonBytes(p2.body));
    expect(pb1).toBe(pb2);
    const a1 = await raw('POST', '/apply', bodyStr);
    const a2 = await raw('POST', '/apply', bodyStr);
    const ab1 = td.decode(canonicalJsonBytes(a1.body));
    const ab2 = td.decode(canonicalJsonBytes(a2.body));
    expect(ab1).toBe(ab2);
  });

  it('DEV_PROOFS gating', async () => {
    const bodyStr = JSON.stringify({ world: 'c', plan: 2 });
    delete process.env.DEV_PROOFS;
    const h0 = makeRawHandler(createHost());
    const r0 = await h0('POST', '/apply', bodyStr);
    const j0 = (r0.body as Resp).journal[0];
    expect(j0.proof).toBeUndefined();
    const canon0 = td.decode(canonicalJsonBytes(JSON.parse(j0.canon)));
    expect(canon0).toBe(j0.canon);

    process.env.DEV_PROOFS = '1';
    const h1 = makeRawHandler(createHost());
    const r1 = await h1('POST', '/apply', bodyStr);
    const j1 = (r1.body as Resp).journal[0];
    const canon1 = td.decode(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(canon1).toBe(j1.canon);
    const hash = blake3hex(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(j1.proof).toBe(hash);
    delete process.env.DEV_PROOFS;
  });

  it('state is ephemeral', async () => {
    const h1 = makeRawHandler(createHost());
    await h1('POST', '/apply', JSON.stringify({ world: 'e', plan: 3 }));
    const r1 = await h1('POST', '/plan', JSON.stringify({ world: 'e', plan: 0 }));
    const w1 = (r1.body as Resp).world;

    const h2 = makeRawHandler(createHost());
    const r2 = await h2('POST', '/plan', JSON.stringify({ world: 'e', plan: 0 }));
    const w2 = (r2.body as Resp).world;
    expect(w1).not.toEqual(w2);
  });

  it('404 for unknown path', async () => {
    const handler = makeRawHandler(createHost());
    const r = await handler('POST', '/nope', '{}');
    expect(r.status).toBe(404);
    const canon = td.decode(canonicalJsonBytes(r.body));
    expect(canon).toBe('{"error":"not_found"}');
  });

  it('404 for wrong method', async () => {
    const handler = makeRawHandler(createHost());
    const r = await handler('GET', '/plan', '{}');
    expect(r.status).toBe(404);
    const canon = td.decode(canonicalJsonBytes(r.body));
    expect(canon).toBe('{"error":"not_found"}');
  });

  it('400 for malformed JSON', async () => {
    const handler = makeRawHandler(createHost());
    const r = await handler('POST', '/plan', '{');
    expect(r.status).toBe(400);
    const canon = td.decode(canonicalJsonBytes(r.body));
    expect(canon).toBe('{"error":"bad_request"}');
  });

  it('bounded cache prevents growth', async () => {
    const host = createHost();
    const handler = makeHandler(host);
    for (let i = 0; i < 40; i++) {
      await handler('POST', '/plan', { world: 'm', plan: i });
    }
    const worldCache = host.cache.get('m');
    expect(worldCache?.size ?? 0).toBeLessThanOrEqual(32);
  });

  it('multi-world cache bounds and map size', async () => {
    const host = createHost();
    const handler = makeHandler(host);
    for (let w = 0; w < 4; w++) {
      for (let i = 0; i < 40; i++) {
        await handler('POST', '/plan', { world: `mw${w}`, plan: i });
      }
    }
    expect(host.cache.size).toBe(4);
    for (let w = 0; w < 4; w++) {
      const worldCache = host.cache.get(`mw${w}`);
      expect(worldCache?.size ?? 0).toBeLessThanOrEqual(32);
    }
  });

  it('no deep imports and .js extensions', async () => {
    const modules = import.meta.glob('../src/**/*.ts', {
      eager: true,
      import: 'default',
      query: '?raw',
    }) as Record<string, string>;
    for (const src of Object.values(modules)) {
      expect(src.includes('../')).toBe(false);
      expect(src.includes('tf-lang-l0/')).toBe(false);
      const importRegex = /from\s+['\"](\.\.?[^'\"]*)['\"]/g;
      let m: RegExpExecArray | null;
      while ((m = importRegex.exec(src))) {
        const p = m[1];
        if (p.startsWith('.')) expect(p.endsWith('.js')).toBe(true);
      }
    }
  });

  it('package exports main', async () => {
    const pkgFiles = import.meta.glob('../package.json', {
      eager: true,
      import: 'default',
      query: '?raw',
    }) as Record<string, string>;
    const pkg = JSON.parse(Object.values(pkgFiles)[0]) as any;
    expect(pkg.main).toBe('src/server.ts');
    expect(pkg.exports).toBe('./src/server.ts');
    expect(Object.keys(pkg.dependencies)).toEqual(['tf-lang-l0']);
  });
});
