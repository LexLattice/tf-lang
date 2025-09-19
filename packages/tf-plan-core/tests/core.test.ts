import { describe, expect, it } from 'vitest';
import {
  computeSpecHash,
  createScore,
  deepFreeze,
  seedRng,
  stableId,
  stableSort,
} from '../src/index.js';

describe('tf-plan-core helpers', () => {
  it('produces deterministic stableId values', () => {
    const a = stableId({ specId: 'spec', component: 'comp', choice: 'choice', seed: 42, version: '1.0.0' });
    const b = stableId({ specId: 'spec', component: 'comp', choice: 'choice', seed: 42, version: '1.0.0' });
    expect(a).toBe(b);
  });

  it('deep freezes nested structures', () => {
    const original = deepFreeze({ foo: { bar: 1 } });
    expect(Object.isFrozen(original)).toBe(true);
    expect(Object.isFrozen(original.foo)).toBe(true);
  });

  it('stableSort preserves order for equals', () => {
    const items = [
      { key: 1, label: 'a' },
      { key: 1, label: 'b' },
      { key: 0, label: 'c' },
    ];
    const sorted = stableSort(items, (a, b) => a.key - b.key);
    expect(sorted.map((item) => item.label)).toEqual(['c', 'a', 'b']);
  });

  it('seedRng generates deterministic sequence', () => {
    const rngA = seedRng(1234);
    const rngB = seedRng(1234);
    const seqA = [rngA.next(), rngA.next(), rngA.next()];
    const seqB = [rngB.next(), rngB.next(), rngB.next()];
    expect(seqA).toEqual(seqB);
  });

  it('createScore aggregates totals', () => {
    const score = createScore({
      complexity: 3,
      risk: 2,
      perf: 5,
      devTime: 1,
      depsReady: 4,
      explain: ['detail'],
    });
    expect(score.total).toBe(3 + 5 + 4 - 2 - 1);
  });

  it('computeSpecHash is stable across property order', () => {
    const specA = { a: 1, b: { c: 2, d: 3 } };
    const specB = { b: { d: 3, c: 2 }, a: 1 };
    expect(computeSpecHash(specA)).toBe(computeSpecHash(specB));
  });
});
