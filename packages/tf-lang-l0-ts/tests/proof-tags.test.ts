import { describe, it, expect } from 'vitest';
import { ProofTag } from '../src/proof/tags.js';

describe('proof tags', () => {
  it('constructs refutation tag', () => {
    const tag: ProofTag = { kind: 'Refutation', code: 'E', msg: 'x' };
    expect(tag.kind).toBe('Refutation');
  });

  it('constructs transport tag', () => {
    const tag: ProofTag = { kind: 'Transport', op: 'LENS_PROJ', region: 'r0' };
    expect(tag.op).toBe('LENS_PROJ');
  });
});
