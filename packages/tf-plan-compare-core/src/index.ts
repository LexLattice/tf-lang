import { PlanNode, stableSort } from '@tf-lang/tf-plan-core';
import { ScaffoldBranch, ScaffoldPlan } from '@tf-lang/tf-plan-scaffold-core';

export const COMPARE_VERSION = '0.1.0';

export type OracleStatus = 'pass' | 'fail' | 'unknown';

export interface OracleSummary {
  readonly branchName: string;
  readonly oracle: string;
  readonly status: OracleStatus;
  readonly details?: string;
  readonly artifact?: string;
}

export interface CompareScore {
  readonly total: number;
  readonly risk: number;
  readonly complexity: number;
  readonly perf: number;
  readonly devTime: number;
  readonly depsReady: number;
}

export interface CompareBranch {
  readonly nodeId: string;
  readonly branchName: string;
  readonly planChoice: string;
  readonly rank: number;
  readonly score: CompareScore;
  readonly summary: string;
  readonly oracles: readonly {
    readonly name: string;
    readonly status: OracleStatus;
    readonly details?: string;
    readonly artifact?: string;
  }[];
}

export interface CompareReport {
  readonly version: string;
  readonly meta: {
    readonly seed: number;
    readonly planVersion: string;
    readonly generatedAt: string;
    readonly notes: readonly string[];
  };
  readonly branches: readonly CompareBranch[];
}

export interface CompareOptions {
  readonly seed?: number;
  readonly oracles?: readonly OracleSummary[];
}

function selectNode(nodes: readonly PlanNode[], branch: ScaffoldBranch): PlanNode | undefined {
  return nodes.find((node) => node.nodeId === branch.nodeId);
}

function mapOracles(summaries: readonly OracleSummary[] | undefined, branchName: string): CompareBranch['oracles'] {
  if (!summaries) {
    return [];
  }
  return summaries
    .filter((summary) => summary.branchName === branchName)
    .map((summary) => ({
      name: summary.oracle,
      status: summary.status,
      details: summary.details,
      artifact: summary.artifact,
    }));
}

function toCompareBranch(node: PlanNode, branch: ScaffoldBranch, rank: number, oracles: CompareBranch['oracles']): CompareBranch {
  return {
    nodeId: node.nodeId,
    branchName: branch.branchName,
    planChoice: node.choice,
    rank,
    score: {
      total: node.score.total,
      risk: node.score.risk,
      complexity: node.score.complexity,
      perf: node.score.perf,
      devTime: node.score.devTime,
      depsReady: node.score.depsReady,
    },
    summary: `${branch.branchName} ranks #${rank} with total ${node.score.total.toFixed(2)} (risk ${node.score.risk.toFixed(2)})`,
    oracles,
  };
}

export function buildCompareReport(
  nodes: readonly PlanNode[],
  scaffold: ScaffoldPlan,
  options: CompareOptions = {},
): CompareReport {
  const seed = options.seed ?? scaffold.meta.seed ?? 42;
  const candidates = scaffold.branches
    .map((branch) => {
      const node = selectNode(nodes, branch);
      if (!node) {
        return undefined;
      }
      return { branch, node };
    })
    .filter((entry): entry is { branch: ScaffoldBranch; node: PlanNode } => entry !== undefined);

  if (candidates.length === 0) {
    throw new Error('No matching branches found between scaffold plan and plan nodes.');
  }

  const ranked = stableSort(candidates, (left, right) => {
    const totalDiff = right.node.score.total - left.node.score.total;
    if (totalDiff !== 0) {
      return totalDiff;
    }
    const riskDiff = left.node.score.risk - right.node.score.risk;
    if (riskDiff !== 0) {
      return riskDiff;
    }
    return left.node.nodeId.localeCompare(right.node.nodeId);
  });

  const branches = ranked.map((entry, index) =>
    toCompareBranch(
      entry.node,
      entry.branch,
      index + 1,
      mapOracles(options.oracles, entry.branch.branchName),
    ),
  );

  return {
    version: COMPARE_VERSION,
    meta: {
      seed,
      planVersion: scaffold.meta.version,
      generatedAt: '1970-01-01T00:00:00.000Z',
      notes: [`branches=${branches.length}`],
    },
    branches,
  };
}
