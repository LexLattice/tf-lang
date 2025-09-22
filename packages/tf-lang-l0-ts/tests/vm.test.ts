// @tf-test kind=product area=runtime speed=fast deps=node

import { describe, it, expect } from 'vitest';
import { VM, Host } from '../src/vm/index.js';
import type { Program } from '../src/model/bytecode.js';
import { DummyHost } from '../src/host/memory.js';

describe('VM', () => {
  it('runs HALT program', async () => {
    const prog: Program = { version: '0.1', regs: 2, instrs: [ { op: 'HALT' } ] };
    const vm = new VM(DummyHost);
    const out = await vm.run(prog);
    expect(out).toBeNull();
  });

  it('basic ops', async () => {
    const prog: Program = {
      version: '0.1',
      regs: 6,
      instrs: [
        { op: 'CONST', dst: 0, value: { state: 1 } },
        { op: 'LENS_PROJ', dst: 1, state: 0, region: 'legal.clauses' },
        { op: 'LENS_MERGE', dst: 2, state: 0, region: 'legal.clauses', sub: 1 },
        { op: 'SNAP_MAKE', dst: 3, state: 2 },
        { op: 'SNAP_ID', dst: 4, snapshot: 3 },
        { op: 'HALT' },
      ],
    };
    const vm = new VM(DummyHost);
    const out = await vm.run(prog);
    expect(out).toBeNull();
  });

  it('law: rewind ∘ apply = id (pair of ids equal)', async () => {
    const prog: Program = {
      version: '0.1',
      regs: 13,
      instrs: [
        // r0 = initial state (array)
        { op: 'CONST', dst: 0, value: [1,2] },
        // r12 = plan value (append 3)
        { op: 'CONST', dst: 12, value: 3 },
        // r1 = snap0, r2 = id0
        { op: 'SNAP_MAKE', dst: 1, state: 0 },
        { op: 'SNAP_ID',   dst: 2, snapshot: 1 },
        // r3 = delta via CALL (state, plan) -> {"append": plan}
        { op: 'CALL', dst: 3, tf_id: 'tf://plan/delta@0.1', args: [0,12] },
        // r4 = state1 after apply
        { op: 'DIFF_APPLY', dst: 4, state: 0, delta: 3 },
        // r5 = snap1, r6 = id1
        { op: 'SNAP_MAKE', dst: 5, state: 4 },
        { op: 'SNAP_ID',   dst: 6, snapshot: 5 },
        // r7 = meta {}
        { op: 'CONST', dst: 7, value: {} },
        // r8 = journal entry
        { op: 'JOURNAL_REC', dst: 8, plan: 12, delta: 3, snap0: 2, snap1: 6, meta: 7 },
        // r9 = world_prev = rewind(world_after, entry)
        { op: 'JOURNAL_REW', dst: 9, world: 4, entry: 8 },
        // r10 = snap_prev, r11 = id_prev
        { op: 'SNAP_MAKE', dst: 10, state: 9 },
        { op: 'SNAP_ID',   dst: 11, snapshot: 10 },
        // r0 = Pack(Pair, id_before, id_prev)
        // r12 = eq(id_before, id_prev)
        { op: 'CALL', dst: 12, tf_id: 'tf://eq/json@0.1', args: [2,11] },
        { op: 'ASSERT', pred: 12, msg: 'rewind law violated' },
        { op: 'PACK', dst: 0, tag: 'Pair', regs: [2,11] },
        { op: 'HALT' },
      ],
    };
    const vm = new VM(DummyHost);
    const out: any = await vm.run(prog);
    expect(out?.replace?.tag).toBe('Pair');
    expect(out?.replace?.values?.[0]).toEqual(out?.replace?.values?.[1]);
  });
});
