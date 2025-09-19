import { describe, expect, it } from 'vitest';
import { PlanNode } from '@tf-lang/tf-plan-core';
import { ScaffoldPlan } from '@tf-lang/tf-plan-scaffold-core';
import { buildCompareReport } from '../src/index.js';

const node = (id: string, total: number, risk: number): PlanNode => ({
  nodeId: id,
  specId: 'spec',
  component: 'branch:spec',
  choice: `choice-${id}`,
  deps: [],
  rationale: 'demo',
  score: {
    total,
    complexity: 4,
    risk,
    perf: 6,
    devTime: 5,
    depsReady: 7,
    explain: ['demo'],
  },
});

const scaffold: ScaffoldPlan = {
  version: '0.1.0',
  template: 'dual-stack',
  generatedAt: '1970-01-01T00:00:00.000Z',
  meta: { seed: 42, specHash: 'hash', version: '0.1.0' },
  branches: [
    {
      nodeId: 'a'.repeat(64),
      branchName: 't4/dual-stack/a',
      workingDir: 'branches/a',
      template: 'dual-stack',
      planChoice: 'choice-a',
      summary: 'summary',
      repoActions: [],
      ciActions: [],
    },
    {
      nodeId: 'b'.repeat(64),
      branchName: 't4/dual-stack/b',
      workingDir: 'branches/b',
      template: 'dual-stack',
      planChoice: 'choice-b',
      summary: 'summary',
      repoActions: [],
      ciActions: [],
    },
  ],
  lookup: {},
};

describe('buildCompareReport', () => {
  it('sorts branches by score and assigns ranks', () => {
    const report = buildCompareReport([
      node('a'.repeat(64), 9, 2),
      node('b'.repeat(64), 8, 1),
    ], scaffold);
    expect(report.branches[0].branchName).toBe('t4/dual-stack/a');
    expect(report.branches[0].rank).toBe(1);
    expect(report.version).toBeDefined();
  });
});
