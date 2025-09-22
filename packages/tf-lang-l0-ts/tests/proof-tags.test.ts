// @tf-test kind=proofs area=runtime speed=fast deps=node

import { describe, it, expect } from 'vitest';
import type { Witness, Normalization, Transport, Refutation, Conservativity, ProofTag } from '../src/proof/index.js';

describe('proof tags', () => {
  it('compile tag shapes', () => {
    const w: Witness = { kind: 'Witness', delta: null, effect: { read: [], write: [], external: [] } };
    const n: Normalization = { kind: 'Normalization', target: 'delta' };
    const t: Transport = { kind: 'Transport', op: 'LENS_PROJ', region: 'r' };
    const r: Refutation = { kind: 'Refutation', code: 'E', msg: 'oops' };
    const c: Conservativity = { kind: 'Conservativity', callee: 'c', expected: 'e', found: 'f' };
    const tags: ProofTag[] = [w, n, t, r, c];
    expect(tags.length).toBe(5);
  });

  it('shape is discriminated by kind', () => {
    const t: ProofTag = { kind: 'Transport', op: 'LENS_PROJ', region: 'r' };
    expect(Object.keys(t).sort()).toEqual(['kind','op','region'].sort());
  });
});
