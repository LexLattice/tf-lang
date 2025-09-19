import { describe, expect, it } from 'vitest';
import { enumeratePlan } from '../src/index.js';
import demoSpec from '../../../tests/specs/demo.json' with { type: 'json' };
import { PlanNode, stableSort } from '@tf-lang/tf-plan-core';

function sortBranches(nodes: readonly PlanNode[]): PlanNode[] {
  return stableSort(nodes, (left, right) => {
    if (right.score.total !== left.score.total) {
      return right.score.total - left.score.total;
    }
    if (left.score.risk !== right.score.risk) {
      return left.score.risk - right.score.risk;
    }
    return left.nodeId.localeCompare(right.nodeId);
  });
}

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

  it('orders branches consistently when applying limits', () => {
    const fullPlan = enumeratePlan(demoSpec, { seed: 42 });
    const fullBranches = fullPlan.nodes.filter((node) => node.component.startsWith('branch:'));
    const sortedFull = sortBranches(fullBranches);

    const maxLimited = enumeratePlan(demoSpec, { seed: 42, maxBranches: 3 });
    const maxBranches = maxLimited.nodes.filter((node) => node.component.startsWith('branch:'));
    expect(maxBranches.map((node) => node.nodeId)).toEqual(sortedFull.slice(0, 3).map((node) => node.nodeId));

    const beamLimited = enumeratePlan(demoSpec, { seed: 42, beamWidth: 2 });
    const beamBranches = beamLimited.nodes.filter((node) => node.component.startsWith('branch:'));
    expect(beamBranches.map((node) => node.nodeId)).toEqual(sortBranches(beamBranches).map((node) => node.nodeId));

    const combined = enumeratePlan(demoSpec, { seed: 42, beamWidth: 2, maxBranches: 2 });
    const combinedBranches = combined.nodes.filter((node) => node.component.startsWith('branch:'));
    const sortedCombined = sortBranches(combinedBranches);
    expect(combinedBranches.map((node) => node.nodeId)).toEqual(sortedCombined.map((node) => node.nodeId));
  });
});
