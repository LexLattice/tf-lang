import { describe, it, expect, afterEach } from 'vitest';
import { devProofsEnabled, __resetEnvCacheForTests__ } from '../../src/util/env.js';
import { withEnv } from '../helpers/env.js';

describe('DEV_PROOFS caching (TS)', () => {
  afterEach(() => __resetEnvCacheForTests__());

  it('reads once, caches, and resets', async () => {
    await withEnv({ DEV_PROOFS: '1' }, () => {
      expect(devProofsEnabled()).toBe(true);
    });
    // Flip env but cache should hold until reset
    await withEnv({ DEV_PROOFS: '0' }, () => {
      expect(devProofsEnabled()).toBe(true);
    });

    __resetEnvCacheForTests__();

    await withEnv({ DEV_PROOFS: '0' }, () => {
      expect(devProofsEnabled()).toBe(false);
    });
  });
});
