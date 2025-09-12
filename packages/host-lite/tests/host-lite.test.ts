import { describe, it, expect } from 'vitest';
import { createServer } from '../src/index.js';
import { canonicalJsonBytes } from '../../tf-lang-l0-ts/src/canon/json.js';
import { blake3hex } from '../../tf-lang-l0-ts/src/canon/hash.js';
import { resetDevProofsForTest } from '../../tf-lang-l0-ts/src/proof/index.js';

async function start(server: any) {
  const port = await new Promise<number>(resolve => server.listen(0, () => resolve((server.address() as any).port)));
  return {
    url: `http://127.0.0.1:${port}`,
    close: () => new Promise<void>(resolve => server.close(() => resolve())),
  };
}

async function post(base: string, path: string, body: any) {
  const res = await fetch(`${base}${path}`, {
    method: 'POST',
    headers: { 'content-type': 'application/json' },
    body: JSON.stringify(body),
  });
  return new Uint8Array(await res.arrayBuffer());
}

describe('host-lite', () => {
  it('idempotent plan and apply', async () => {
    const h = await start(createServer());
    const body = { plan: 1 };
    const r1 = await post(h.url, '/plan', body);
    const r2 = await post(h.url, '/plan', body);
    expect(Buffer.from(r1).toString()).toBe(Buffer.from(r2).toString());
    await h.close();

    const h2 = await start(createServer());
    const a1 = await post(h2.url, '/apply', body);
    const a2 = await post(h2.url, '/apply', body);
    expect(Buffer.from(a1).toString()).toBe(Buffer.from(a2).toString());
    await h2.close();
  });

  it('canonical journal stable', async () => {
    const h = await start(createServer());
    const body = { plan: 2 };
    const b1 = await post(h.url, '/apply', body);
    const j1 = JSON.parse(Buffer.from(b1).toString()).journal;
    const canon1 = canonicalJsonBytes(JSON.parse(Buffer.from(b1).toString()));
    expect(Buffer.from(b1)).toEqual(Buffer.from(canon1));
    await h.close();
    const h2 = await start(createServer());
    const b2 = await post(h2.url, '/apply', body);
    const j2 = JSON.parse(Buffer.from(b2).toString()).journal;
    await h2.close();
    const h1 = blake3hex(canonicalJsonBytes(j1));
    const h2b = blake3hex(canonicalJsonBytes(j2));
    expect(h1).toBe(h2b);
  });

  it('proof gating', async () => {
    process.env.DEV_PROOFS = '1';
    resetDevProofsForTest();
    const h = await start(createServer());
    const b1 = await post(h.url, '/apply', { plan: 3 });
    await h.close();
    expect(JSON.parse(Buffer.from(b1).toString()).proof).toBeDefined();
    process.env.DEV_PROOFS = '0';
    resetDevProofsForTest();
    const h2 = await start(createServer());
    const b2 = await post(h2.url, '/apply', { plan: 3 });
    await h2.close();
    expect('proof' in JSON.parse(Buffer.from(b2).toString())).toBe(false);
  });

  it('state is ephemeral', async () => {
    const h = await start(createServer());
    await post(h.url, '/apply', { plan: 4 });
    await h.close();
    const h2 = await start(createServer());
    const w = JSON.parse(Buffer.from(await post(h2.url, '/plan', { plan: 0 })).toString()).world;
    await h2.close();
    expect(w).toEqual([]);
  });
});
