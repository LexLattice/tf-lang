// @tf-test kind=product area=plan speed=fast deps=node
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

  it('applies beamWidth and maxBranches after sorting', () => {
    const baseline = enumeratePlan(demoSpec, { seed: 42 });
    const branchNodes = baseline.nodes.filter((node) => node.component.startsWith('branch:'));
    const sortedBranchIds = branchNodes.map((node) => node.nodeId);

    const beamPlan = enumeratePlan(demoSpec, { seed: 42, beamWidth: 1 });
    const beamBranchIds = beamPlan.nodes
      .filter((node) => node.component.startsWith('branch:'))
      .map((node) => node.nodeId);
    expect(beamBranchIds).toEqual(sortedBranchIds.slice(0, 1));

    const maxPlan = enumeratePlan(demoSpec, { seed: 42, maxBranches: 2 });
    const maxBranchIds = maxPlan.nodes
      .filter((node) => node.component.startsWith('branch:'))
      .map((node) => node.nodeId);
    expect(maxBranchIds).toEqual(sortedBranchIds.slice(0, 2));

    const combinedPlan = enumeratePlan(demoSpec, { seed: 42, beamWidth: 2, maxBranches: 2 });
    const combinedBranchIds = combinedPlan.nodes
      .filter((node) => node.component.startsWith('branch:'))
      .map((node) => node.nodeId);
    expect(combinedBranchIds).toEqual(sortedBranchIds.slice(0, 2));
  });
});
