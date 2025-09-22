// @tf-test kind=product area=runtime speed=fast deps=node

import { describe, it, expect } from 'vitest';
import { makeHandler, createHost } from 'host-lite-ts';

describe('C1: lru-multiworld', () => {
  it('per-world cap == 32 and cache map size == number of worlds touched', async () => {
    const host = createHost();
    const handler = makeHandler(host);

    // Touch 4 worlds with >32 entries each
    const worlds = 4;
    for (let w = 0; w < worlds; w++) {
      for (let i = 0; i < 40; i++) {
        await handler('POST', '/plan', { world: `mw${w}`, plan: i });
      }
    }

    expect(host.cache.size).toBe(worlds);
    for (let w = 0; w < worlds; w++) {
      const worldCache = host.cache.get(`mw${w}`);
      expect(worldCache?.size ?? 0).toBeLessThanOrEqual(32);
    }
  });
});
