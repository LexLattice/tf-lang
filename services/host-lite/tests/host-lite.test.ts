import { describe, it, expect } from 'vitest';
import { createServer } from '../src/server.js';
import { canonicalJsonBytes, blake3hex } from '../../../packages/tf-lang-l0-ts/src/index.js';

const td = new TextDecoder();

interface Resp { world: unknown; delta: unknown; journal: { canon: string; proof?: string }[] }

describe('host-lite', () => {
  it('idempotent plan and apply', async () => {
    const srv = createServer();
    const body = { world: 'w', plan: 1 };
    const p1 = await srv.inject({ method: 'POST', url: '/plan', payload: body });
    const p2 = await srv.inject({ method: 'POST', url: '/plan', payload: body });
    expect(p1.body).toBe(p2.body);
    const a1 = await srv.inject({ method: 'POST', url: '/apply', payload: body });
    const a2 = await srv.inject({ method: 'POST', url: '/apply', payload: body });
    expect(a1.body).toBe(a2.body);
    await srv.close();
  });

  it('canonical journal and proof gating', async () => {
    delete process.env.DEV_PROOFS;
    const srv0 = createServer();
    const b = { world: 'c', plan: 2 };
    const r0 = await srv0.inject({ method: 'POST', url: '/apply', payload: b });
    const out0 = JSON.parse(r0.body) as Resp;
    const j0 = out0.journal[0];
    expect(j0.proof).toBeUndefined();
    const canon0 = td.decode(canonicalJsonBytes(JSON.parse(j0.canon)));
    expect(canon0).toBe(j0.canon);
    await srv0.close();

    process.env.DEV_PROOFS = '1';
    const srv1 = createServer();
    const r1 = await srv1.inject({ method: 'POST', url: '/apply', payload: b });
    const out1 = JSON.parse(r1.body) as Resp;
    const j1 = out1.journal[0];
    const canon1 = td.decode(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(canon1).toBe(j1.canon);
    const hash = blake3hex(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(j1.proof).toBe(hash);
    await srv1.close();
    delete process.env.DEV_PROOFS;
  });

  it('state is ephemeral', async () => {
    const srv = createServer();
    await srv.inject({ method: 'POST', url: '/apply', payload: { world: 'e', plan: 3 } });
    const r1 = await srv.inject({ method: 'POST', url: '/plan', payload: { world: 'e', plan: 0 } });
    const w1 = (JSON.parse(r1.body) as Resp).world;
    await srv.close();

    const srv2 = createServer();
    const r2 = await srv2.inject({ method: 'POST', url: '/plan', payload: { world: 'e', plan: 0 } });
    const w2 = (JSON.parse(r2.body) as Resp).world;
    expect(w1).not.toEqual(w2);
    await srv2.close();
  });
});
