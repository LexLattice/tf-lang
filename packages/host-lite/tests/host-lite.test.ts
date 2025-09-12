import { describe, it, expect } from 'vitest';
import { readFileSync } from 'node:fs';
import { canonicalJsonBytes, blake3hex } from 'tf-lang-l0';
import { createHost } from '../src/index.js';

const td = new TextDecoder();

interface Resp { world: unknown; delta: unknown; journal: { canon: string; proof?: string }[] }

describe('host-lite', () => {
  it('idempotent plan and apply', async () => {
    const h = createHost();
    const body = { world: 'w', plan: 1 };
    const p1 = await h.request({ method: 'POST', path: '/plan', body });
    const p2 = await h.request({ method: 'POST', path: '/plan', body });
    expect(p1.body).toBe(p2.body);
    const a1 = await h.request({ method: 'POST', path: '/apply', body });
    const a2 = await h.request({ method: 'POST', path: '/apply', body });
    expect(a1.body).toBe(a2.body);
  });

  it('canonical journal and proof gating', async () => {
    delete process.env.DEV_PROOFS;
    const h0 = createHost();
    const b = { world: 'c', plan: 2 };
    const r0 = await h0.request({ method: 'POST', path: '/apply', body: b });
    const out0 = JSON.parse(r0.body) as Resp;
    const j0 = out0.journal[0];
    expect(j0.proof).toBeUndefined();
    const canon0 = td.decode(canonicalJsonBytes(JSON.parse(j0.canon)));
    expect(canon0).toBe(j0.canon);

    process.env.DEV_PROOFS = '1';
    const h1 = createHost();
    const r1 = await h1.request({ method: 'POST', path: '/apply', body: b });
    const out1 = JSON.parse(r1.body) as Resp;
    const j1 = out1.journal[0];
    const canon1 = td.decode(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(canon1).toBe(j1.canon);
    const hash = blake3hex(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(j1.proof).toBe(hash);
    delete process.env.DEV_PROOFS;
  });

  it('state is ephemeral', async () => {
    const h = createHost();
    await h.request({ method: 'POST', path: '/apply', body: { world: 'e', plan: 3 } });
    const r1 = await h.request({ method: 'POST', path: '/plan', body: { world: 'e', plan: 0 } });
    const w1 = (JSON.parse(r1.body) as Resp).world;

    const h2 = createHost();
    const r2 = await h2.request({ method: 'POST', path: '/plan', body: { world: 'e', plan: 0 } });
    const w2 = (JSON.parse(r2.body) as Resp).world;
    expect(w1).not.toEqual(w2);
  });

  it('404 for unknown path', async () => {
    const h = createHost();
    const r = await h.request({ method: 'POST', path: '/nope', body: {} });
    expect(r.statusCode).toBe(404);
    const err = td.decode(canonicalJsonBytes({ error: 'not found' }));
    expect(r.body).toBe(err);
  });

  it('cache bounded to avoid growth', async () => {
    const h = createHost();
    for (let i = 0; i < 40; i++) {
      await h.request({ method: 'POST', path: '/plan', body: { world: 'm', plan: i } });
    }
    const stats = h.stats();
    expect(stats.entries).toBeLessThanOrEqual(16);
    expect(stats.worlds).toBeLessThanOrEqual(16);
  });

  it('no deep imports across packages', () => {
    const src = readFileSync(new URL('../src/index.ts', import.meta.url), 'utf8');
    const re = /from '\.\.\/\.\./g;
    expect(re.test(src)).toBe(false);
  });
});
