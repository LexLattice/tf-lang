import { describe, it, expect, afterEach } from 'vitest';
import { VM } from '../src/vm/index.js';
import type { Program } from '../src/model/bytecode.js';
import { DummyHost } from '../src/host/memory.js';
import { flush } from '../src/proof/index.js';
import { withEnv } from './helpers/env.js';
import { __resetEnvCacheForTests__ } from '../src/util/env.js';

describe('proof dev mode', () => {
  afterEach(() => __resetEnvCacheForTests__());
  const prog: Program = {
    version: '0.1',
    regs: 2,
    instrs: [
      { op: 'CONST', dst: 0, value: {} },
      { op: 'LENS_PROJ', dst: 1, state: 0, region: 'r' },
      { op: 'CONST', dst: 0, value: { x: 1 } },
      { op: 'HALT' },
    ],
  };

  it('emits tags when DEV_PROOFS=1', async () => {
    await withEnv({ DEV_PROOFS: '1' }, async () => {
      const vm = new VM(DummyHost);
      await vm.run(prog);
      const tags = flush();
      expect(tags.some(t => t.kind === 'Transport')).toBe(true);
      expect(tags.some(t => t.kind === 'Witness')).toBe(true);
    });
  });

  it('no tags when DEV_PROOFS is unset', async () => {
    await withEnv({ DEV_PROOFS: undefined }, async () => {
      const vm = new VM(DummyHost);
      await vm.run(prog);
      const tags = flush();
      expect(tags.length).toBe(0);
    });
  });
});
