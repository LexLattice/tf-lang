import type { Host } from '../vm/index.js';
import type { Value } from '../model/index.js';

function deepEqual(a: unknown, b: unknown): boolean {
  try { return JSON.stringify(a) === JSON.stringify(b); } catch { return false; }
}

export const DummyHost: Host = {
  lens_project: async (state, region) => ({ region, state }),
  lens_merge: async (state, _region, sub) => ({ orig: state, sub }),
  snapshot_make: async (state) => state,
  snapshot_id: async (snap) => `id:${JSON.stringify(snap)}`,
  diff: async (a, b) => {
    if (deepEqual(a, b)) return null;
    return { replace: b };
  },
  diff_apply: async (state, delta) => {
    if (delta == null) return state;                 // identity
    if (delta && typeof delta === 'object' && 'replace' in delta) return (delta as any).replace;
    // old logic
    if (Array.isArray(state) && delta && typeof delta === 'object' && 'append' in delta) {
      return [...state, (delta as any).append];
    }
    return state;
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