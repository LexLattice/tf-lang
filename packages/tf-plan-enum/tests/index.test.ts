import { describe, expect, it } from 'vitest';
import { enumeratePlan } from '../src/index.js';
import demoSpec from '../../../tests/specs/demo.json' with { type: 'json' };

describe('enumeratePlan', () => {
  it('produces deterministic branch nodes for the same seed', () => {
    const first = enumeratePlan(demoSpec, { seed: 42, beamWidth: 3, maxBranches: 5 });
    const second = enumeratePlan(demoSpec, { seed: 42, beamWidth: 3, maxBranches: 5 });
    expect(first.meta.specHash).toEqual(second.meta.specHash);
    expect(first.nodes.map((node) => node.nodeId)).toEqual(second.nodes.map((node) => node.nodeId));
  });

  it('creates at least three branch nodes with rationales', () => {
    const plan = enumeratePlan(demoSpec, { seed: 42, beamWidth: 3 });
    const branchNodes = plan.nodes.filter((node) => node.component.startsWith('branch:'));
    expect(branchNodes.length).toBeGreaterThanOrEqual(3);
    branchNodes.forEach((node) => {
      expect(node.rationale.length).toBeGreaterThan(0);
      expect(node.score.explain.length).toBeGreaterThan(0);
    });
  });
});
