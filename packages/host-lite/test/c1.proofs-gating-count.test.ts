// @tf-test kind=proofs area=runtime speed=fast deps=node
import { describe, it, expect } from 'vitest';
import { makeRawHandler, makeHandler, createHost } from 'host-lite-ts';
import { canonicalJsonBytes, blake3hex } from 'tf-lang-l0';

interface JournalEntry { canon: string; proof?: string }
interface Resp { world: unknown; delta: unknown; journal: JournalEntry[] }

const td = new TextDecoder();

describe('C1: proofs-gating-count', () => {
  it('DEV_PROOFS off: 0 proof tags; on: >0; no extra work when off', async () => {
    const bodyStr = JSON.stringify({ world: 'c', plan: 2 });

    // Off: expect 0 proof tags and canonical self-encoding
    delete process.env.DEV_PROOFS;
    const h0 = makeRawHandler({ makeHandler: makeHandler(createHost()) });
    const r0 = await h0('POST', '/apply', bodyStr);
    const j0 = (r0.body as Resp).journal[0];
    expect(Object.keys(j0)).toEqual(['canon']);
    const canon0 = td.decode(canonicalJsonBytes(JSON.parse(j0.canon)));
    expect(canon0).toBe(j0.canon);

    // On: expect >0 proof tags
    process.env.DEV_PROOFS = '1';
    const h1 = makeRawHandler({ makeHandler: makeHandler(createHost()) });
    const r1 = await h1('POST', '/apply', bodyStr);
    const j1 = (r1.body as Resp).journal[0];
    const canon1 = td.decode(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(canon1).toBe(j1.canon);
    const hash = blake3hex(canonicalJsonBytes(JSON.parse(j1.canon)));
    expect(j1.proof).toBe(hash);

    // Cleanup flag
    delete process.env.DEV_PROOFS;
  });
});
