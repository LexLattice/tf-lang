import { describe, it, expect, afterEach } from 'vitest';
import { VM } from '../src/vm/interpreter.js';
import { DummyHost } from '../src/host/memory.js';
import type { Program } from '../src/model/bytecode.js';

afterEach(() => {
  delete process.env.DEV_PROOFS;
});

describe('DEV_PROOFS emission', () => {
  it('emits witness and transport tags', async () => {
    process.env.DEV_PROOFS = '1';
    const prog: Program = {
      version: '0.1',
      regs: 3,
      instrs: [
        { op: 'CONST', dst: 0, value: [] },
        { op: 'CONST', dst: 1, value: { append: 1 } },
        { op: 'DIFF_APPLY', dst: 0, state: 0, delta: 1 },
        { op: 'LENS_PROJ', dst: 2, state: 0, region: 'r' },
        { op: 'HALT' },
      ],
    };
    const vm = new VM(DummyHost);
    await vm.run(prog);
    expect(vm.tags?.some(t => t.kind === 'Witness')).toBe(true);
    expect(vm.tags?.filter(t => t.kind === 'Normalization').length).toBeGreaterThan(0);
    expect(vm.tags?.some(t => t.kind === 'Transport' && t.op === 'LENS_PROJ')).toBe(true);
  });

  it('emits refutation on ASSERT failure', async () => {
    process.env.DEV_PROOFS = '1';
    const prog: Program = {
      version: '0.1',
      regs: 1,
      instrs: [
        { op: 'CONST', dst: 0, value: 0 },
        { op: 'ASSERT', pred: 0, msg: 'no' },
      ],
    };
    const vm = new VM(DummyHost);
    await expect(vm.run(prog)).rejects.toThrow();
    expect(vm.tags?.some(t => t.kind === 'Refutation')).toBe(true);
  });

  it('emits conservativity on missing call', async () => {
    process.env.DEV_PROOFS = '1';
    const prog: Program = {
      version: '0.1',
      regs: 1,
      instrs: [
        { op: 'CALL', dst: 0, tf_id: 'tf://missing@0.1', args: [] },
        { op: 'HALT' },
      ],
    };
    const vm = new VM(DummyHost);
    await vm.run(prog);
    expect(vm.tags?.some(t => t.kind === 'Conservativity')).toBe(true);
  });

  it('is silent when DEV_PROOFS unset', async () => {
    const prog: Program = { version: '0.1', regs: 1, instrs: [ { op: 'HALT' } ] };
    const vm = new VM(DummyHost);
    await vm.run(prog);
    expect(vm.tags).toBeUndefined();
  });
});
