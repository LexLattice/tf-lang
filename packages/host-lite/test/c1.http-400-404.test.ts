// @tf-test kind=product area=host speed=fast deps=node
import { describe, it, expect } from 'vitest';
import { makeRawHandler, makeHandler, createHost } from 'host-lite-ts';
import { canonicalJsonBytes } from 'tf-lang-l0';

const td = new TextDecoder();

describe('C1: http-400-404', () => {
  it('malformed JSON → 400; non-POST or unknown path → 404 canonical', async () => {
    const handler = makeRawHandler({ makeHandler: makeHandler(createHost()) });

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
});
