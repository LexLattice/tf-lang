import { describe, it, expect, afterEach } from 'vitest';
import { createHostLite } from '../src/host/http-lite.js';
import { canonicalJsonBytes } from '../src/canon/json.js';
import { resetDevProofsForTest } from '../src/proof/index.js';
import type { Server } from 'node:http';

async function startServer(): Promise<{ server: Server; base: string }> {
  const server = createHostLite();
  await new Promise(res => server.listen(0, res));
  const port = (server.address() as any).port;
  return { server, base: `http://127.0.0.1:${port}` };
}

describe('host-lite', () => {
  let server: Server | undefined;
  let base = '';
  afterEach(async () => {
    if (server) await new Promise(res => server!.close(res));
    server = undefined;
    resetDevProofsForTest();
    delete process.env.DEV_PROOFS;
  });

  it('idempotent plan and apply', async () => {
    ({ server, base } = await startServer());
    const body = { world: 'w', plan: 1 };
    const init = { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify(body) };
    const r1 = await fetch(base + '/plan', init);
    const t1 = await r1.text();
    const r2 = await fetch(base + '/plan', init);
    const t2 = await r2.text();
    expect(t1).toBe(t2);

    const a1 = await fetch(base + '/apply', init);
    const at1 = await a1.text();
    const a2 = await fetch(base + '/apply', init);
    const at2 = await a2.text();
    expect(at1).toBe(at2);

    const p = await fetch(base + '/plan', { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify({ world: 'w', plan: 2 }) });
    const obj = await p.json();
    expect(obj.world).toEqual([1, 2]);
  });

  it('canonical responses and proof gating', async () => {
    ({ server, base } = await startServer());
    const r = await fetch(base + '/plan', { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify({ world: 'x', plan: 1 }) });
    const text = await r.text();
    const parsed = JSON.parse(text);
    const canon = Buffer.from(canonicalJsonBytes(parsed)).toString();
    expect(text).toBe(canon);
    expect(parsed.proofs).toBeUndefined();
    await new Promise(res => server!.close(res));

    resetDevProofsForTest();
    process.env.DEV_PROOFS = '1';
    ({ server, base } = await startServer());
    const r2 = await fetch(base + '/plan', { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify({ world: 'x', plan: 1 }) });
    const obj2 = await r2.json();
    expect(Array.isArray(obj2.proofs)).toBe(true);
  });

  it('world state is ephemeral', async () => {
    ({ server, base } = await startServer());
    await fetch(base + '/apply', { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify({ world: 'w', plan: 1 }) });
    await new Promise(res => server!.close(res));

    ({ server, base } = await startServer());
    const r = await fetch(base + '/plan', { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify({ world: 'w', plan: 2 }) });
    const obj = await r.json();
    expect(obj.world).toEqual([2]);
  });
});
