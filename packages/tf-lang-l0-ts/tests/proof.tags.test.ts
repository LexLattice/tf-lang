import { describe, it, expect } from 'vitest';
import { Effects } from '../src/model/types.js';
import type {
  Witness,
  Normalization,
  Transport,
  Refutation,
  Conservativity,
  ProofTag,
} from '../src/index.js';

describe('proof tags', () => {
  it('constructs tag shapes', () => {
    const w: Witness = { kind: 'Witness', delta: null, effect: new Effects() };
    const n: Normalization = { kind: 'Normalization', target: 'delta' };
    const t: Transport = { kind: 'Transport', op: 'LENS_PROJ', region: 'r1' };
    const r: Refutation = { kind: 'Refutation', code: 'X', msg: 'oops' };
    const c: Conservativity = {
      kind: 'Conservativity',
      callee: 'f',
      expected: 'a',
      found: 'b',
    };
    const tags: ProofTag[] = [w, n, t, r, c];
    expect(tags).toHaveLength(5);
  });
});
