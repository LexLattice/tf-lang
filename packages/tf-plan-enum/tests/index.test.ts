import { describe, expect, it } from 'vitest';
import { enumeratePlan } from '../src/index.js';
import demoSpec from '../../../tests/specs/demo.json' with { type: 'json' };

const compareNodes = (left: ReturnType<typeof enumeratePlan>['nodes'][number], right: ReturnType<typeof enumeratePlan>['nodes'][number]): number => {
  const totalDiff = right.score.total - left.score.total;
  if (totalDiff !== 0) {
    return totalDiff;
  }
  const riskDiff = left.score.risk - right.score.risk;
  if (riskDiff !== 0) {
    return riskDiff;
  }
  return left.nodeId.localeCompare(right.nodeId);
};

function sortedBranchIds(planNodes: readonly ReturnType<typeof enumeratePlan>['nodes'][number][]): string[] {
  return planNodes
    .filter((node) => node.component.startsWith('branch:'))
    .slice()
    .sort(compareNodes)
    .map((node) => node.nodeId);
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

  it('honours maxBranches by selecting the top-ranked branch nodes', () => {
    const full = enumeratePlan(demoSpec, { seed: 42 });
    const limited = enumeratePlan(demoSpec, { seed: 42, maxBranches: 2 });
    const expected = sortedBranchIds(full.nodes).slice(0, 2);
    const actual = sortedBranchIds(limited.nodes);
    expect(actual).toEqual(expected);
  });

  it('applies beamWidth before ranking branch nodes', () => {
    const beamWidth = 2;
    const full = enumeratePlan(demoSpec, { seed: 42 });
    const narrowed = enumeratePlan(demoSpec, { seed: 42, beamWidth });

    const componentNodes = full.nodes.filter((node) => !node.component.startsWith('branch:'));
    const grouped = componentNodes.reduce<Record<string, typeof componentNodes[number][]>>( (acc, node) => {
      (acc[node.component] ??= []).push(node);
      return acc;
    }, {});
    const allowedByComponent = new Map<string, Set<string>>();

    for (const [componentId, nodes] of Object.entries(grouped)) {
      const topNodes = nodes.slice().sort(compareNodes).slice(0, beamWidth);
      const allowed = allowedByComponent.get(componentId) ?? new Set<string>();
      topNodes.forEach((node) => allowed.add(node.nodeId));
      allowedByComponent.set(componentId, allowed);
    }

    const nodeById = new Map(componentNodes.map((node) => [node.nodeId, node] as const));

    const expected = full.nodes
      .filter((node) => node.component.startsWith('branch:'))
      .filter((branch) =>
        branch.deps.every((dependency) => {
          const componentNode = nodeById.get(dependency);
          if (!componentNode) {
            return false;
          }
          return allowedByComponent.get(componentNode.component)?.has(dependency) ?? false;
        }),
      )
      .sort(compareNodes)
      .slice(0, narrowed.nodes.filter((node) => node.component.startsWith('branch:')).length)
      .map((node) => node.nodeId);

    const actual = sortedBranchIds(narrowed.nodes);
    expect(actual).toEqual(expected);
  });

  it('combines beamWidth and maxBranches deterministically', () => {
    const base = enumeratePlan(demoSpec, { seed: 42 });
    const constrained = enumeratePlan(demoSpec, { seed: 42, beamWidth: 2, maxBranches: 1 });
    const expected = sortedBranchIds(base.nodes).slice(0, 1);
    const actual = sortedBranchIds(constrained.nodes);
    expect(actual).toEqual(expected);
  });
});
