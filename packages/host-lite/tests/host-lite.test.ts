import { describe, it, expect, beforeEach, vi } from 'vitest';
import { makeHandler, createHost, makeRawHandler } from '../src/server.js';
import { canonicalJsonBytes } from 'tf-lang-l0';
import { readdir, readFile } from 'node:fs/promises';
import { extname } from 'node:path';

const td = new TextDecoder();

interface JournalEntry { canon: string; proof?: string }
interface Resp { world: unknown; delta: unknown; journal: JournalEntry[] }

const blakeCalls: number[] = [];

vi.mock('tf-lang-l0', async (importOriginal) => {
  const mod = await importOriginal<typeof import('tf-lang-l0')>();
  return {
    ...mod,
    blake3hex: (bytes: Uint8Array) => {
      blakeCalls.push(1);
      return mod.blake3hex(bytes);
    },
  };
});

beforeEach(() => {
  blakeCalls.length = 0;
  delete process.env.DEV_PROOFS;
});

describe('host-lite', () => {
  it('byte-identical determinism for plan/apply', async () => {
    const handler = makeRawHandler();
    const body = '{"world":"d","plan":1}';
    const p1 = await handler('POST', '/plan', body);
    const p2 = await handler('POST', '/plan', body);
    expect(td.decode(canonicalJsonBytes(p1.body))).toBe(
      td.decode(canonicalJsonBytes(p2.body)),
    );
    const a1 = await handler('POST', '/apply', body);
    const a2 = await handler('POST', '/apply', body);
    expect(td.decode(canonicalJsonBytes(a1.body))).toBe(
      td.decode(canonicalJsonBytes(a2.body)),
    );
  });

  it('DEV_PROOFS gating without overhead', async () => {
    const h0 = makeRawHandler();
    const r0 = await h0('POST', '/apply', '{"world":"g0","plan":1}');
    const j0 = (r0.body as Resp).journal[0];
    expect(j0.proof).toBeUndefined();
    expect(blakeCalls.length).toBe(1);

    blakeCalls.length = 0;
    process.env.DEV_PROOFS = '1';
    const h1 = makeRawHandler();
    const r1 = await h1('POST', '/apply', '{"world":"g1","plan":1}');
    const j1 = (r1.body as Resp).journal[0];
    expect(j1.proof).toBeDefined();
    expect(blakeCalls.length).toBe(2);
  });

  it('404 for unknown routes and non-POST; 400 for malformed JSON', async () => {
    const handler = makeRawHandler();
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

  it('multi-world cache capped and map size matches', async () => {
    const host = createHost();
    const handler = makeHandler(host);
    const worlds = ['mw0', 'mw1', 'mw2', 'mw3'];
    for (const w of worlds) {
      for (let i = 0; i < 40; i++) {
        await handler('POST', '/plan', { world: w, plan: i });
      }
    }
    expect(host.cache.size).toBe(worlds.length);
    for (const w of worlds) {
      const wc = host.cache.get(w);
      expect(wc?.size ?? 0).toBeLessThanOrEqual(32);
    }
  });

  it('no deep imports and relative imports include .js', async () => {
    const dir = new URL('../src/', import.meta.url);
    const entries = await readdir(dir);
    for (const f of entries) {
      if (extname(f) !== '.ts') continue;
      const src = await readFile(new URL(f, dir), 'utf8');
      expect(src.includes('../')).toBe(false);
      expect(/from ['"]tf-lang-l0\//.test(src)).toBe(false);
      const rel = src.match(/from ['"](\.\.\/|\.\/[^'\"]*)['"]/g) || [];
      for (const imp of rel) {
        const m = /from ['"]([^'\"]+)['"]/.exec(imp);
        if (m && (m[1].startsWith('./') || m[1].startsWith('../'))) {
          expect(m[1].endsWith('.js')).toBe(true);
        }
      }
    }
  });
});

