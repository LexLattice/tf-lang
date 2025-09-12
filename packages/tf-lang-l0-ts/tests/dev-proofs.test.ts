import { describe, it, expect } from 'vitest';
import { VM } from '../src/vm/interpreter.js';
import type { Program } from '../src/model/bytecode.js';
import type { Host } from '../src/vm/opcode.js';
import { take } from '../src/proof/sink.js';

function stubHost(overrides: Partial<Host> = {}): Host {
  return {
    lens_project: (s) => s,
    lens_merge: (s) => s,
    snapshot_make: (s) => s,
    snapshot_id: () => '',
    diff_apply: (s) => s,
    diff_invert: (d) => d,
    journal_record: () => ({ value: null }),
    journal_rewind: () => ({ value: null }),
    call_tf: () => null,
    ...overrides,
  } as Host;
}

describe('dev proofs', () => {
  it('emits tags when DEV_PROOFS=1', async () => {
    process.env.DEV_PROOFS = '1';
    const host = stubHost();
    const vm = new VM(host);
    const prog: Program = { regs: 2, instrs: [
      { op: 'CONST', dst: 0, value: {} },
      { op: 'LENS_PROJ', dst: 1, state: 0, region: '/r' },
    ]};
    await vm.run(prog);
    const tags = take();
    expect(tags.some(t => t.kind === 'Transport')).toBe(true);
    expect(tags.some(t => t.kind === 'Witness')).toBe(true);
    delete process.env.DEV_PROOFS;
  });

  it('no tags when DEV_PROOFS unset', async () => {
    delete process.env.DEV_PROOFS;
    const host = stubHost();
    const vm = new VM(host);
    const prog: Program = { regs: 1, instrs: [{ op: 'CONST', dst: 0, value: null }] };
    await vm.run(prog);
    expect(take()).toEqual([]);
  });

  it('refutation tag on ASSERT failure', async () => {
    process.env.DEV_PROOFS = '1';
    const host = stubHost();
    const vm = new VM(host);
    const prog: Program = { regs: 1, instrs: [
      { op: 'CONST', dst: 0, value: false },
      { op: 'ASSERT', pred: 0, msg: 'oops' },
    ]};
    await expect(vm.run(prog)).rejects.toThrow('ASSERT failed');
    const tags = take();
    expect(tags.some(t => t.kind === 'Refutation' && t.code === 'ASSERT')).toBe(true);
    delete process.env.DEV_PROOFS;
  });

  it('conservativity tag on CALL failure', async () => {
    process.env.DEV_PROOFS = '1';
    const host = stubHost({ call_tf: () => { throw new Error('bad'); } });
    const vm = new VM(host);
    const prog: Program = { regs: 1, instrs: [ { op: 'CALL', dst: 0, tf_id: 'x', args: [] } ] };
    await expect(vm.run(prog)).rejects.toThrow('bad');
    const tags = take();
    expect(tags.some(t => t.kind === 'Conservativity' && t.callee === 'x')).toBe(true);
    delete process.env.DEV_PROOFS;
  });
});
