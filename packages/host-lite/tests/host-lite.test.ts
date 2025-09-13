import { describe, it, expect } from 'vitest';
import { makeHandler, makeRawHandler, createHost } from '../src/server.js';
import { canonicalJsonBytes, blake3hex } from 'tf-lang-l0';
import { readFile, readdir } from 'node:fs/promises';
import { join } from 'node:path';

const td = new TextDecoder();

interface JournalEntry { canon: string; proof?: string }
interface Resp { world: unknown; delta: unknown; journal: JournalEntry[] }

async function gatherTs(dir: string, acc: string[] = []): Promise<string[]> {
  const entries = await readdir(dir, { withFileTypes: true });
  for (const e of entries) {
    const p = join(dir, e.name);
    if (e.isDirectory()) {
      if (e.name === 'node_modules') continue;
      await gatherTs(p, acc);
    }
    else if (p.endsWith('.ts')) acc.push(p);
  }
  return acc;
}

describe('host-lite', () => {
  it('byte-identical determinism', async () => {
    const raw = makeRawHandler(createHost());
    const body = JSON.stringify({ world: 'w', plan: 1 });
    const p1 = await raw('POST', '/plan', body);
    const p2 = await raw('POST', '/plan', body);
    expect(p1.status).toBe(200);
    expect(td.decode(canonicalJsonBytes(p1.body))).toBe(td.decode(canonicalJsonBytes(p2.body)));
    const a1 = await raw('POST', '/apply', body);
    const a2 = await raw('POST', '/apply', body);
    expect(td.decode(canonicalJsonBytes(a1.body))).toBe(td.decode(canonicalJsonBytes(a2.body)));
  });

  it('DEV_PROOFS gating', async () => {
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
    expect(j1.canon).toBe(j0.canon);
    const hash = blake3hex(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(j1.proof).toBe(hash);
    delete process.env.DEV_PROOFS;
  });

  it('404 and 400 errors', async () => {
    const raw = makeRawHandler(createHost());
    const notFound = await raw('POST', '/nope', '{}');
    expect(notFound.status).toBe(404);
    expect(td.decode(canonicalJsonBytes(notFound.body))).toBe('{"error":"not_found"}');
    const wrongMethod = await raw('GET', '/plan', '{}');
    expect(wrongMethod.status).toBe(404);
    expect(td.decode(canonicalJsonBytes(wrongMethod.body))).toBe('{"error":"not_found"}');
    const bad = await raw('POST', '/plan', '{');
    expect(bad.status).toBe(400);
    expect(td.decode(canonicalJsonBytes(bad.body))).toBe('{"error":"bad_request"}');
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

  it('no deep imports in src', async () => {
    const files = await gatherTs(new URL('../src', import.meta.url).pathname);
    for (const f of files) {
      const src = await readFile(f, 'utf8');
      expect(src.includes("from '../")).toBe(false);
      expect(src.includes("from \"tf-lang-l0/")).toBe(false);
      expect(src.includes("from 'tf-lang-l0/")).toBe(false);
    }
  });

  it('ESM imports include .js', async () => {
    const files = await gatherTs(new URL('..', import.meta.url).pathname);
    for (const f of files) {
      const src = await readFile(f, 'utf8');
      const lines = src.split('\n');
      for (const line of lines) {
        const m = line.match(/from\s+['\"](\.\.\/[^'\"]+|\.\/[^'\"]+)'/);
        if (m && !m[1].endsWith('.js')) {
          throw new Error(`missing .js in import at ${f}: ${line}`);
        }
      }
    }
  });

  it('package exports main src', async () => {
    const pkg = JSON.parse(await readFile(new URL('../package.json', import.meta.url), 'utf8'));
    expect(pkg.main).toBe('src/server.ts');
    expect(pkg.exports).toBe('./src/server.ts');
    expect(Object.keys(pkg.dependencies)).toEqual(['tf-lang-l0']);
  });
});
