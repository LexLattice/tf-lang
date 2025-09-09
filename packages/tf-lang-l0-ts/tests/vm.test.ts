
import { describe, it, expect } from 'vitest';
import { VM, Host } from '../src/vm/index.js';
import type { Program } from '../src/model/bytecode.js';

const DummyHost: Host = {
  lens_project: async (state, region) => ({ region, state }),
  lens_merge: async (state, _region, sub) => ({ orig: state, sub }),
  snapshot_make: async (state) => state,
  snapshot_id: async (snap) => `id:${JSON.stringify(snap)}`,
  diff_apply: async (state, delta) => {
    // delta = { append: v } on array states
    if (Array.isArray(state) && delta && typeof delta === 'object' && 'append' in delta) {
      return [...state, (delta as any).append];
    }
    return delta;
  },
  diff_invert: async (delta) => ({ invert: delta }),
  journal_record: async (_plan, delta, s0, s1, _meta) => ({ value: { delta, from: s0, to: s1 } }),
  journal_rewind: async (world, entry) => {
    const w = Array.isArray(world.value) ? [...world.value] : world.value;
    if (Array.isArray(w) && entry.value?.delta && 'append' in entry.value.delta) {
      w.pop();
    }
    return { value: w };
  },
  call_tf: async (id, args) => {
    if (id === 'tf://plan/delta@0.1') {
      return { append: args[1] };
    }
    if (id === 'tf://plan/simulate@0.1') {
      return { delta: args[1] ?? null, world: args[0] ?? null };
    }
    if (id === 'tf://eq/json@0.1') {
      return JSON.stringify(args[0]) === JSON.stringify(args[1]);
    }
    return null;
  },
};

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
    expect(out?.tag).toBe('Pair');
    expect(out?.values?.[0]).toEqual(out?.values?.[1]);
  });
});
