// @tf-test kind=product area=runtime speed=fast deps=node

import { describe, it, expect } from 'vitest';
import { makeHandler, createHost } from 'host-lite-ts';

describe('C1 — apply persists', () => {
  it('updates world state for subsequent calls', async () => {
    const host = createHost();
    const handler = makeHandler(host);

    // apply mutation to w1
    const a = await handler('POST', '/apply', { world: 'w1', plan: { op: 'x' } });
    expect(a.status).toBe(200);

    // plan on same world observes new base state
    const p = await handler('POST', '/plan', { world: 'w1', plan: { op: 'y' } });
    const rWorld = (p.body as any).world;

    // sanity: a fresh host would not include 'x'
    const fresh = makeHandler(createHost());
    const p2 = await fresh('POST', '/plan', { world: 'w1', plan: { op: 'y' } });
    const r2World = (p2.body as any).world;

    expect(JSON.stringify(rWorld)).not.toEqual(JSON.stringify(r2World));
  });
});

