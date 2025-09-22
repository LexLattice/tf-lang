// @tf-test kind=proofs area=runtime speed=fast deps=node

import { describe, it, expect, afterEach, beforeEach, vi } from 'vitest';
import type { Program } from '../src/model/bytecode.js';

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

async function loadModules() {
  const [{ VM }, { DummyHost }, proof] = await Promise.all([
    import('../src/vm/index.js'),
    import('../src/host/memory.js'),
    import('../src/proof/index.js'),
  ]);
  return { VM, DummyHost, flush: proof.flush, reset: proof.resetDevProofsForTest };
}

describe('proof dev mode', () => {
  beforeEach(() => {
    vi.resetModules();
  });

  afterEach(() => {
    delete process.env.DEV_PROOFS;
    vi.resetModules();
  });

  it('emits tags when DEV_PROOFS=1', async () => {
    process.env.DEV_PROOFS = '1';
    const { VM, DummyHost, flush, reset } = await loadModules();
    const vm = new VM(DummyHost);
    await vm.run(prog);
    const tags = flush();
    expect(tags.some(t => t.kind === 'Transport')).toBe(true);
    expect(tags.some(t => t.kind === 'Witness')).toBe(true);
    reset();
  });

  it('no tags when DEV_PROOFS is unset', async () => {
    const { VM, DummyHost, flush } = await loadModules();
    const vm = new VM(DummyHost);
    await vm.run(prog);
    const tags = flush();
    expect(tags.length).toBe(0);
  });

  it('reset clears cached log state', async () => {
    process.env.DEV_PROOFS = '1';
    const modules = await loadModules();
    const vm = new modules.VM(modules.DummyHost);
    await vm.run(prog);
    expect(modules.flush().length).toBeGreaterThan(0);

    modules.reset();
    expect(modules.flush().length).toBe(0);
  });
});
