import { describe, expect, it } from 'vitest';
import { complexity, depsReady, devTime, perf, risk, scorePlanNode } from '../src/index.js';

describe('tf-plan-scoring', () => {
  it('scores individual dimensions deterministically', () => {
    const comp = complexity('create_vm', 'aws_t3.micro');
    const riskScore = risk('create_vm', 'aws_t3.micro');
    const perfScore = perf('create_vm', 'aws_t3.micro');
    const dev = devTime('create_vm', 'aws_t3.micro');
    const deps = depsReady('create_vm', 'aws_t3.micro');
    expect(comp.value).toBeGreaterThan(0);
    expect(riskScore.value).toBeGreaterThan(0);
    expect(perfScore.value).toBeGreaterThan(0);
    expect(dev.value).toBeGreaterThan(0);
    expect(deps.value).toBeGreaterThan(0);
  });

  it('aggregates scorePlanNode explain entries', () => {
    const score = scorePlanNode({ component: 'copy', choice: 'direct' });
    expect(score.explain.length).toBeGreaterThan(0);
    expect(typeof score.total).toBe('number');
  });
});
