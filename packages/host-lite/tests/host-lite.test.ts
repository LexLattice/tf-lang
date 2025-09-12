import { describe, it, expect } from 'vitest';
import { createHost } from '../src/index.js';
import { canonicalJsonBytes, blake3hex } from 'tf-lang-l0';

const td = new TextDecoder();

interface Resp { world: unknown; delta: unknown; journal: { canon: string; proof?: string }[] }

function req(path: string, body: unknown) {
  return new Request(`http://localhost${path}`, {
    method: 'POST',
    body: JSON.stringify(body),
    headers: { 'content-type': 'application/json' },
  });
}

describe('host-lite', () => {
  it('idempotent plan and apply', async () => {
    const host = createHost();
    const body = { world: 'w', plan: 1 };
    const p1 = await host.handle(req('/plan', body));
    const p2 = await host.handle(req('/plan', body));
    expect(await p1.text()).toBe(await p2.text());
    const a1 = await host.handle(req('/apply', body));
    const a2 = await host.handle(req('/apply', body));
    const t1 = await a1.text();
    const t2 = await a2.text();
    expect(t1).toBe(t2);
    const stats = host.stats();
    expect(stats.worlds).toBe(1);
    expect(stats.applies).toBe(1);
  });

  it('canonical journal and proof gating', async () => {
    const host0 = createHost();
    const b = { world: 'c', plan: 2 };
    const r0 = await host0.handle(req('/apply', b));
    const out0 = JSON.parse(await r0.text()) as Resp;
    const j0 = out0.journal[0];
    expect(j0.proof).toBeUndefined();
    const canon0 = td.decode(canonicalJsonBytes(JSON.parse(j0.canon)));
    expect(canon0).toBe(j0.canon);

    process.env.DEV_PROOFS = '1';
    const host1 = createHost();
    const r1 = await host1.handle(req('/apply', b));
    const out1 = JSON.parse(await r1.text()) as Resp;
    const j1 = out1.journal[0];
    const canon1 = td.decode(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(canon1).toBe(j1.canon);
    const hash = blake3hex(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(j1.proof).toBe(hash);
    delete process.env.DEV_PROOFS;
  });

  it('state is ephemeral', async () => {
    const host1 = createHost();
    await host1.handle(req('/apply', { world: 'e', plan: 3 }));
    const r1 = await host1.handle(req('/plan', { world: 'e', plan: 0 }));
    const w1 = (JSON.parse(await r1.text()) as Resp).world;
    const host2 = createHost();
    const r2 = await host2.handle(req('/plan', { world: 'e', plan: 0 }));
    const w2 = (JSON.parse(await r2.text()) as Resp).world;
    expect(w1).not.toEqual(w2);
  });

  it('returns 404 for non-endpoints', async () => {
    const host = createHost();
    const r = await host.handle(req('/nope', {}));
    expect(r.status).toBe(404);
    const text = await r.text();
    expect(text).toBe(td.decode(canonicalJsonBytes({ error: 'not_found' })));
  });

  it('cache does not grow with distinct inputs', async () => {
    const host = createHost();
    for (let i = 0; i < 5; i++) {
      await host.handle(req('/apply', { world: 'g', plan: i }));
    }
    const stats = host.stats();
    expect(stats.worlds).toBe(1);
    expect(stats.applies).toBe(1);
  });
});
