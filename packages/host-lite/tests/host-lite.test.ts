import { describe, it, expect } from 'vitest';
import { createHostLite } from '../src/server.js';
import { canonicalJsonBytes, blake3hex } from 'tf-lang-l0';
import { execSync } from 'node:child_process';

const td = new TextDecoder();

interface Resp { world: unknown; delta: unknown; journal: { canon: string; proof?: string }[] }

describe('host-lite', () => {
  it('idempotent plan and apply', async () => {
    const host = createHostLite();
    const body = { world: 'w', plan: 1 };
    const p1 = await host.handle('POST', '/plan', body);
    const p2 = await host.handle('POST', '/plan', body);
    expect(p1.body).toBe(p2.body);
    const a1 = await host.handle('POST', '/apply', body);
    const a2 = await host.handle('POST', '/apply', body);
    expect(a1.body).toBe(a2.body);
  });

  it('canonical journal and proof gating', async () => {
    const host0 = createHostLite();
    const b = { world: 'c', plan: 2 };
    const r0 = await host0.handle('POST', '/apply', b);
    const out0 = JSON.parse(r0.body) as Resp;
    const j0 = out0.journal[0];
    expect(j0.proof).toBeUndefined();
    const canon0 = td.decode(canonicalJsonBytes(JSON.parse(j0.canon)));
    expect(canon0).toBe(j0.canon);

    process.env.DEV_PROOFS = '1';
    const host1 = createHostLite();
    const r1 = await host1.handle('POST', '/apply', b);
    const out1 = JSON.parse(r1.body) as Resp;
    const j1 = out1.journal[0];
    const canon1 = td.decode(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(canon1).toBe(j1.canon);
    const hash = blake3hex(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(j1.proof).toBe(hash);
    delete process.env.DEV_PROOFS;
  });

  it('state is ephemeral', async () => {
    const host1 = createHostLite();
    await host1.handle('POST', '/apply', { world: 'e', plan: 3 });
    const r1 = await host1.handle('POST', '/plan', { world: 'e', plan: 0 });
    const w1 = (JSON.parse(r1.body) as Resp).world;

    const host2 = createHostLite();
    const r2 = await host2.handle('POST', '/plan', { world: 'e', plan: 0 });
    const w2 = (JSON.parse(r2.body) as Resp).world;
    expect(w1).not.toEqual(w2);
  });

  it('returns 404 for unknown paths', async () => {
    const host = createHostLite();
    const r = await host.handle('POST', '/unknown', { world: 'x', plan: 0 });
    expect(r.status).toBe(404);
    expect(r.body).toBe(td.decode(canonicalJsonBytes({ error: 'not_found' })));
  });

  it('cache bounded', async () => {
    const host = createHostLite();
    for (let i = 0; i < 20; i++) {
      await host.handle('POST', '/plan', { world: 'g', plan: i });
    }
    expect(host.cacheSize('g')).toBeLessThanOrEqual(16);
  });

  it('no deep package imports', () => {
    const out = execSync("rg '\\.\\./\\.\\./' src tests -l || true").toString().trim();
    expect(out).toBe('');
  });
});
