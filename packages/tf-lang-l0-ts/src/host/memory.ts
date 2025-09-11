import type { Host } from '../vm/index.js';
import { canonicalJsonBytes } from '../canon/json.js';
import { blake3hex } from '../canon/hash.js';
import { registry as opsRegistry } from '../ops/index.js';

export const DummyHost: Host = {
  lens_project: async (state, region) => ({ region, state }),
  lens_merge: async (state, _region, sub) => ({ orig: state, sub }),
  snapshot_make: async (state) => state,
  snapshot_id: async (snap) => `id:${blake3hex(canonicalJsonBytes(snap))}`,
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
      const a = canonicalJsonBytes(args[0]);
      const b = canonicalJsonBytes(args[1]);
      return Buffer.from(a).equals(Buffer.from(b));
    }
    return await opsRegistry.call(id, args);
  },
};