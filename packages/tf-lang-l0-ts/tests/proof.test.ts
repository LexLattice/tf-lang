import { describe, it, expect } from 'vitest';
import { proof } from '../src/index.js';

describe('proof tags', () => {
  it('constructs tag variants', () => {
    const w: proof.Witness = { kind: 'Witness', delta: null, effect: { read: [], write: [], external: [] } };
    const n: proof.Normalization = { kind: 'Normalization', target: 'delta' };
    const t: proof.Transport = { kind: 'Transport', op: 'LENS_PROJ', region: '/r' };
    const r: proof.Refutation = { kind: 'Refutation', code: 'E_X' };
    const c: proof.Conservativity = { kind: 'Conservativity', callee: 'c', expected: 'e', found: 'f' };
    const kinds = [w, n, t, r, c].map(x => x.kind);
    expect(kinds).toEqual(['Witness', 'Normalization', 'Transport', 'Refutation', 'Conservativity']);
  });
});
