// @tf-test kind=product area=plan speed=fast deps=node
import { describe, expect, it } from 'vitest';
import {
  PLAN_GRAPH_VERSION,
  canonicalStringify,
  deepFreeze,
  hashObject,
  seedRng,
  stableId,
  stableSort,
  parseSpecId,
} from '../src/index.ts';

describe('PLAN_GRAPH_VERSION', () => {
  it('is pinned for deterministic outputs', () => {
    expect(PLAN_GRAPH_VERSION).toBe('0.1.0');
  });
});

describe('stableId', () => {
  it('produces deterministic hashes and short ids', () => {
    const first = stableId({
      scope: 'branch',
      specId: 'demo',
      component: 'transfer',
      choice: 'rsync',
      seed: 42,
      version: PLAN_GRAPH_VERSION,
    });

    const second = stableId({
      scope: 'branch',
      specId: 'demo',
      component: 'transfer',
      choice: 'rsync',
      seed: 42,
      version: PLAN_GRAPH_VERSION,
    });

    expect(first.full).toEqual(second.full);
    expect(first.short).toEqual(second.short);
    expect(first.short).toHaveLength(12);
  });
});

describe('deepFreeze', () => {
  it('freezes nested structures without mutating the original reference', () => {
    const input = { foo: { bar: [1, 2, 3] } };
    const frozen = deepFreeze(input);

    expect(() => {
      (frozen as { foo: { bar: number[] } }).foo.bar.push(4);
    }).toThrow();

    expect(Object.isFrozen(frozen)).toBe(true);
    expect(Object.isFrozen((frozen as { foo: unknown }).foo)).toBe(true);
  });
});

describe('stableSort', () => {
  it('keeps the original order for equal elements', () => {
    const input = [
      { value: 2, id: 'a' },
      { value: 1, id: 'b' },
      { value: 1, id: 'c' },
      { value: 3, id: 'd' },
    ];
    const sorted = stableSort(input, (left, right) => left.value - right.value);
    expect(sorted.map((entry) => entry.id)).toEqual(['b', 'c', 'a', 'd']);
  });
});

describe('seedRng', () => {
  it('produces deterministic sequences for the same seed', () => {
    const rngA = seedRng(42);
    const rngB = seedRng(42);
    const seqA = [rngA.next(), rngA.next(), rngA.next()];
    const seqB = [rngB.next(), rngB.next(), rngB.next()];
    expect(seqA).toEqual(seqB);
  });

  it('produces values in the expected range for nextInt', () => {
    const rng = seedRng(123);
    for (let i = 0; i < 20; i += 1) {
      const value = rng.nextInt(5);
      expect(value).toBeGreaterThanOrEqual(0);
      expect(value).toBeLessThan(5);
    }
  });
});

describe('canonicalStringify', () => {
  it('orders object keys recursively for determinism', () => {
    const first = canonicalStringify({
      b: 2,
      a: { z: 3, y: [2, 1] },
    });
    const second = canonicalStringify({
      a: { y: [2, 1], z: 3 },
      b: 2,
    });
    expect(first).toEqual(second);
    expect(first).toEqual('{"a":{"y":[2,1],"z":3},"b":2}');
  });
});

describe('hashObject', () => {
  it('derives the hash from the canonical stringification', () => {
    const hash = hashObject({ foo: 1, bar: 2 });
    expect(hash).toHaveLength(64);
    const same = hashObject({ bar: 2, foo: 1 });
    expect(hash).toEqual(same);
  });
});

describe('parseSpecId', () => {
  it('extracts the short spec hash from a valid specId', () => {
    expect(parseSpecId('demo:deadbeef').specHash).toBe('deadbeef');
  });
  it('rejects invalid formats with helpful messages', () => {
    expect(() => parseSpecId('invalid')).toThrow(/expected format '<name>:<8 hex>'/);
    expect(() => parseSpecId('name:BADHASH')).toThrow(/8 lowercase hex/);
  });
});
