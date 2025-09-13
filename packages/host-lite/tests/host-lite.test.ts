import { describe, it, expect } from 'vitest';
import { makeHandler, createHost, makeRawHandler } from 'host-lite-ts';
import { canonicalJsonBytes, blake3hex } from 'tf-lang-l0';
import { readdir, readFile } from 'node:fs/promises';
import { join } from 'node:path';

const td = new TextDecoder();

interface JournalEntry { canon: string; proof?: string }
interface Resp { world: unknown; delta: unknown; journal: JournalEntry[] }

async function collectTs(dir: string): Promise<string[]> {
  const entries = await readdir(dir, { withFileTypes: true });
  const files: string[] = [];
  for (const e of entries) {
    const p = join(dir, e.name);
    if (e.isDirectory()) files.push(...(await collectTs(p)));
    else if (p.endsWith('.ts')) files.push(p);
  }
  return files;
}

describe('host-lite', () => {
  it('byte-identical plan and apply', async () => {
    const host = createHost();
    const handler = makeRawHandler(host);
    const bodyStr = JSON.stringify({ world: 'w', plan: 1 });
    const p1 = await handler('POST', '/plan', bodyStr);
    const p2 = await handler('POST', '/plan', bodyStr);
    expect(td.decode(canonicalJsonBytes(p1.body))).toBe(td.decode(canonicalJsonBytes(p2.body)));
    const a1 = await handler('POST', '/apply', bodyStr);
    const a2 = await handler('POST', '/apply', bodyStr);
    expect(td.decode(canonicalJsonBytes(a1.body))).toBe(td.decode(canonicalJsonBytes(a2.body)));
  });

  it('DEV_PROOFS gating', async () => {
    const bodyStr = JSON.stringify({ world: 'c', plan: 2 });
    delete process.env.DEV_PROOFS;
    const h0 = makeRawHandler(createHost());
    const r0 = await h0('POST', '/apply', bodyStr);
    const j0 = (r0.body as Resp).journal[0];
    expect(Object.keys(j0)).toEqual(['canon']);
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

  it('404 and 400 errors', async () => {
    const handler = makeRawHandler(createHost());
    const r1 = await handler('POST', '/nope', '{}');
    expect(r1.status).toBe(404);
    expect(td.decode(canonicalJsonBytes(r1.body))).toBe('{"error":"not_found"}');
    const r2 = await handler('GET', '/plan', '{}');
    expect(r2.status).toBe(404);
    expect(td.decode(canonicalJsonBytes(r2.body))).toBe('{"error":"not_found"}');
    const r3 = await handler('POST', '/plan', '{');
    expect(r3.status).toBe(400);
    expect(td.decode(canonicalJsonBytes(r3.body))).toBe('{"error":"bad_request"}');
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

  it('bounded cache prevents growth', async () => {
    const host = createHost();
    const handler = makeHandler(host);
    for (let i = 0; i < 40; i++) {
      await handler('POST', '/plan', { world: 'm', plan: i });
    }
    const worldCache = host.cache.get('m');
    expect(worldCache?.size ?? 0).toBeLessThanOrEqual(32);
  });

  it('multi-world cache bounds', async () => {
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
    const root = new URL('..', import.meta.url).pathname;
    const files = await collectTs(root);
    for (const file of files) {
      const src = await readFile(file, 'utf8');
      const importRegex = /import\s+[^'";]+['"]([^'"]+)['"]/g;
      let m: RegExpExecArray | null;
      while ((m = importRegex.exec(src))) {
        const p = m[1];
        expect(p.includes('../')).toBe(false);
        expect(p.includes('tf-lang-l0/')).toBe(false);
        if (p.startsWith('.')) expect(p.endsWith('.js')).toBe(true);
      }
    }
  });

  it('package exports main', async () => {
    const pkg = JSON.parse(await readFile(new URL('../package.json', import.meta.url), 'utf8'));
    expect(pkg.main).toBe('src/server.ts');
    expect(pkg.exports).toBe('./src/server.ts');
  });
});
