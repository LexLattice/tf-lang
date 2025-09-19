import { describe, expect, it } from 'vitest';
import { PlanNode } from '@tf-lang/tf-plan-core';
import { createScaffoldPlan } from '../src/index.js';

const baseMeta = { seed: 42, specHash: 'hash', version: '0.1.0' } as const;

function makeNode(total: number, risk: number, id: string): PlanNode {
  return {
    nodeId: id,
    specId: 'spec',
    component: 'branch:spec',
    choice: `choice-${id}`,
    deps: [],
    rationale: 'demo',
    score: {
      total,
      complexity: 5,
      risk,
      perf: 6,
      devTime: 4,
      depsReady: 7,
      explain: ['demo'],
    },
  };
}

describe('createScaffoldPlan', () => {
  it('selects top branches and produces deterministic mapping', () => {
    const nodes: PlanNode[] = [makeNode(8, 3, 'a'.repeat(64)), makeNode(9, 2, 'b'.repeat(64)), makeNode(9, 4, 'c'.repeat(64))];
    const plan = createScaffoldPlan(nodes, baseMeta, { template: 'dual-stack', top: 2 });
    expect(plan.branches).toHaveLength(2);
    expect(plan.branches[0].branchName).toContain('dual-stack');
    expect(plan.lookup[plan.branches[0].nodeId].workingDir).toBe(plan.branches[0].workingDir);
  });
});
