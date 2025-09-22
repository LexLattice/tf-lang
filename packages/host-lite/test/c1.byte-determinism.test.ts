// @tf-test kind=infra area=host speed=fast deps=node
import { describe, it, expect } from 'vitest';
import { makeRawHandler, makeHandler, createHost } from 'host-lite-ts';
import { canonicalJsonBytes } from 'tf-lang-l0';

const td = new TextDecoder();

describe('C1: byte-determinism', () => {
  it('two identical POSTs to /plan and /apply produce byte-identical responses', async () => {
    const host = createHost();
    const handler = makeRawHandler({ makeHandler: makeHandler(host) });
    const bodyStr = JSON.stringify({ world: 'w', plan: 1 });

    const p1 = await handler('POST', '/plan', bodyStr);
    const p2 = await handler('POST', '/plan', bodyStr);
    expect(td.decode(canonicalJsonBytes(p1.body))).toBe(td.decode(canonicalJsonBytes(p2.body)));

    const a1 = await handler('POST', '/apply', bodyStr);
    const a2 = await handler('POST', '/apply', bodyStr);
    expect(td.decode(canonicalJsonBytes(a1.body))).toBe(td.decode(canonicalJsonBytes(a2.body)));
  });
});
