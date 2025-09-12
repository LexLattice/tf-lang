import { describe, it, expect } from 'vitest';
import { createHostLite } from '../src/server.js';
import fs from 'fs';

async function start(proofs = false) {
  if (proofs) process.env.DEV_PROOFS = '1';
  else delete process.env.DEV_PROOFS;
  const srv = createHostLite();
  await new Promise<void>(res => srv.listen(0, res));
  const port = (srv.address() as any).port;
  return { srv, base: `http://127.0.0.1:${port}` };
}

describe('host-lite', () => {
  it('idempotent plan/apply', async () => {
    const { srv, base } = await start();
    const planBody = { world: [], plan: { append: 1 } };
    const r1 = await (await fetch(base + '/plan', { method: 'POST', body: JSON.stringify(planBody) })).text();
    const r2 = await (await fetch(base + '/plan', { method: 'POST', body: JSON.stringify(planBody) })).text();
    expect(r1).toBe(r2);

    const applyBody = { world: [], delta: { append: 1 } };
    const a1 = await (await fetch(base + '/apply', { method: 'POST', body: JSON.stringify(applyBody) })).text();
    const a2 = await (await fetch(base + '/apply', { method: 'POST', body: JSON.stringify(applyBody) })).text();
    expect(a1).toBe(a2);
    await new Promise(res => srv.close(res));
  });

  it('canonical journal entries', async () => {
    const { srv, base } = await start();
    const body = { world: [], delta: { b: 1, a: 2 } };
    const res = await fetch(base + '/apply', { method: 'POST', body: JSON.stringify(body) });
    const json = await res.json();
    expect(JSON.stringify(json.journal[0].value)).toBe('{"delta":{"a":2,"b":1},"from":"s0","to":"s1"}');
    await new Promise(res => srv.close(res));
  });

  it('proof gating', async () => {
    let { srv, base } = await start(true);
    let res = await fetch(base + '/plan', { method: 'POST', body: '{}' });
    const withProof = await res.json();
    expect(withProof.journal[0].proof).toBeDefined();
    await new Promise(res => srv.close(res));

    ({ srv, base } = await start(false));
    res = await fetch(base + '/plan', { method: 'POST', body: '{}' });
    const withoutProof = await res.json();
    expect(withoutProof.journal[0].proof).toBeUndefined();
    await new Promise(res => srv.close(res));
  });

  it('no fs writes', async () => {
    const before = fs.readdirSync('.');
    const { srv, base } = await start();
    await fetch(base + '/plan', { method: 'POST', body: '{}' });
    await fetch(base + '/apply', { method: 'POST', body: '{}' });
    await new Promise(res => srv.close(res));
    const after = fs.readdirSync('.');
    expect(after.sort()).toEqual(before.sort());
  });
});

