// @tf-test kind=product area=plan speed=fast deps=node
import { describe, expect, it } from 'vitest';
import { scorePlanNode } from '../src/index.js';

describe('scorePlanNode', () => {
  it('produces deterministic totals for the same input', () => {
    const first = scorePlanNode({ component: 'transfer', choice: 'managed rsync pipeline', seed: 42 });
    const second = scorePlanNode({ component: 'transfer', choice: 'managed rsync pipeline', seed: 42 });
    expect(first.total).toEqual(second.total);
    expect(first.explain.length).toBeGreaterThan(0);
  });

  it('yields different totals when the choice changes', () => {
    const first = scorePlanNode({ component: 'transfer', choice: 'managed rsync pipeline', seed: 42 });
    const second = scorePlanNode({ component: 'transfer', choice: 'prototype delta sync', seed: 42 });
    expect(first.total).not.toEqual(second.total);
  });
});
