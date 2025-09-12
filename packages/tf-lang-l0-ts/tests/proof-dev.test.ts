import { describe, it, expect, beforeEach } from 'vitest';
import { VM } from '../src/vm/index.js';
import type { Program } from '../src/model/bytecode.js';
import { DummyHost } from '../src/host/memory.js';
import { flush, devProofsEnabled, resetDevProofsForTest } from '../src/proof/index.js';

describe('proof dev mode', () => {
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

  beforeEach(() => {
    resetDevProofsForTest();
    delete process.env.DEV_PROOFS;
  });

  it('emits tags when DEV_PROOFS=1', async () => {
    process.env.DEV_PROOFS = '1';
    const vm = new VM(DummyHost);
    await vm.run(prog);
    const tags = flush();
    expect(tags.some(t => t.kind === 'Transport')).toBe(true);
    expect(tags.some(t => t.kind === 'Witness')).toBe(true);
  });

  it('no tags when DEV_PROOFS is unset', async () => {
    const vm = new VM(DummyHost);
    await vm.run(prog);
    const tags = flush();
    expect(tags.length).toBe(0);
  });

  it('caches env and resets', () => {
    process.env.DEV_PROOFS = '1';
    expect(devProofsEnabled()).toBe(true);
    delete process.env.DEV_PROOFS;
    expect(devProofsEnabled()).toBe(true); // cached
    resetDevProofsForTest();
    expect(devProofsEnabled()).toBe(false);
  });
});
