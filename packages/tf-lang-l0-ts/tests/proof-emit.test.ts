import { describe, test, expect, beforeEach } from 'vitest';
import { vm } from '../src/index.js';
import { DummyHost } from '../src/host/memory.js';
import { take } from '../src/proof/dev.js';

const { VM } = vm;

describe('proof tag emission', () => {
  beforeEach(() => { take(); });

  test('no tags without DEV_PROOFS', async () => {
    delete process.env.DEV_PROOFS;
    const v = new VM(DummyHost);
    const prog = {
      regs: 3,
      instrs: [
        { op: 'CONST', dst: 0, value: { a: 1 } },
        { op: 'LENS_PROJ', dst: 1, state: 0, region: 'r' },
        { op: 'CALL', dst: 2, tf_id: 'tf://missing@0.1', args: [] },
        { op: 'HALT' },
      ],
    } as any;
    await v.run(prog);
    expect(take()).toHaveLength(0);
  });

  test('tags emitted when DEV_PROOFS=1', async () => {
    process.env.DEV_PROOFS = '1';
    const v = new VM(DummyHost);
    const prog = {
      regs: 3,
      instrs: [
        { op: 'CONST', dst: 0, value: { a: 1 } },
        { op: 'LENS_PROJ', dst: 1, state: 0, region: 'r' },
        { op: 'CALL', dst: 2, tf_id: 'tf://missing@0.1', args: [] },
        { op: 'HALT' },
      ],
    } as any;
    await v.run(prog);
    const tags = take();
    expect(tags.some(t => t.kind === 'Witness')).toBe(true);
    expect(tags.filter(t => t.kind === 'Normalization').length).toBeGreaterThan(0);
    expect(tags.some(t => t.kind === 'Transport')).toBe(true);
    expect(tags.some(t => t.kind === 'Conservativity')).toBe(true);

    take();
    const prog2 = {
      regs: 1,
      instrs: [
        { op: 'CONST', dst: 0, value: false },
        { op: 'ASSERT', pred: 0, msg: 'nope' },
      ],
    } as any;
    await expect(v.run(prog2)).rejects.toThrow(/ASSERT failed/);
    const tags2 = take();
    expect(tags2.some(t => t.kind === 'Refutation')).toBe(true);
  });
});
