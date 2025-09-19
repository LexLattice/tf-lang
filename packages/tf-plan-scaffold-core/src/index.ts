import { PlanNode, stableSort } from '@tf-lang/tf-plan-core';

export const SCAFFOLD_VERSION = '0.1.0';

export type TemplateKind = 'ts' | 'rs' | 'dual-stack';

export interface PlanSummaryMeta {
  readonly seed: number;
  readonly specHash: string;
  readonly version: string;
}

export interface RepoAction {
  readonly type: 'checkout' | 'createBranch' | 'applyTemplate' | 'updateScripts';
  readonly params: Record<string, unknown>;
}

export interface CiAction {
  readonly type: 'workflow';
  readonly path: string;
  readonly uses: string;
  readonly with: Record<string, unknown>;
}

export interface ScaffoldBranch {
  readonly nodeId: string;
  readonly branchName: string;
  readonly workingDir: string;
  readonly template: TemplateKind;
  readonly planChoice: string;
  readonly summary: string;
  readonly repoActions: readonly RepoAction[];
  readonly ciActions: readonly CiAction[];
}

export interface ScaffoldPlan {
  readonly version: string;
  readonly template: TemplateKind;
  readonly generatedAt: string;
  readonly meta: PlanSummaryMeta;
  readonly branches: readonly ScaffoldBranch[];
  readonly lookup: Readonly<Record<string, { branchName: string; workingDir: string }>>;
}

export interface ScaffoldOptions {
  readonly template: TemplateKind;
  readonly top: number;
  readonly baseBranch?: string;
  readonly workingDirPrefix?: string;
}

function pickBranchNodes(nodes: readonly PlanNode[]): PlanNode[] {
  return nodes.filter((node) => node.component.startsWith('branch:'));
}

function defaultWorkingDir(node: PlanNode, prefix = 'branches'): string {
  return `${prefix}/${node.nodeId.slice(0, 12)}`;
}

function defaultBranchName(node: PlanNode, template: TemplateKind): string {
  const suffix = node.nodeId.slice(0, 12);
  return `t4/${template}/${suffix}`;
}

function createRepoActions(branchName: string, template: TemplateKind, baseBranch: string): RepoAction[] {
  return [
    {
      type: 'checkout',
      params: { base: baseBranch },
    },
    {
      type: 'createBranch',
      params: { name: branchName },
    },
    {
      type: 'applyTemplate',
      params: { template },
    },
    {
      type: 'updateScripts',
      params: {
        scripts: {
          't4:oracle': 'pnpm tf-check run --mode=ci',
          't4:report': 'pnpm tf-plan compare --plan out/t4/plan/plan.ndjson --inputs out/t4/scaffold/index.json --out out/t4/compare',
        },
      },
    },
  ];
}

function createCiActions(branchName: string): CiAction[] {
  const workflowName = `.github/workflows/${branchName.replace(/\//g, '-')}.yml`;
  return [
    {
      type: 'workflow',
      path: workflowName,
      uses: '.github/workflows/reusable-tf-check.yml',
      with: {
        branch: branchName,
        upload: true,
      },
    },
  ];
}

export function createScaffoldPlan(
  nodes: readonly PlanNode[],
  meta: PlanSummaryMeta,
  options: ScaffoldOptions,
): ScaffoldPlan {
  if (options.top <= 0) {
    throw new Error('Scaffold requires at least one branch to select.');
  }
  const branchNodes = pickBranchNodes(nodes);
  if (branchNodes.length === 0) {
    throw new Error('No branch nodes available for scaffolding.');
  }

  const sorted = stableSort(branchNodes, (left, right) => {
    const totalDiff = right.score.total - left.score.total;
    if (totalDiff !== 0) {
      return totalDiff;
    }
    const riskDiff = left.score.risk - right.score.risk;
    if (riskDiff !== 0) {
      return riskDiff;
    }
    return left.nodeId.localeCompare(right.nodeId);
  });

  const chosen = sorted.slice(0, options.top);
  const baseBranch = options.baseBranch ?? 'main';
  const generatedAt = '1970-01-01T00:00:00.000Z';
  const branches: ScaffoldBranch[] = chosen.map((node) => {
    const branchName = defaultBranchName(node, options.template);
    const workingDir = defaultWorkingDir(node, options.workingDirPrefix ?? 'branches');
    const repoActions = createRepoActions(branchName, options.template, baseBranch);
    const ciActions = createCiActions(branchName);
    const summary = `${branchName} tracks ${node.choice} (total ${node.score.total.toFixed(2)})`;
    return {
      nodeId: node.nodeId,
      branchName,
      workingDir,
      template: options.template,
      planChoice: node.choice,
      summary,
      repoActions,
      ciActions,
    };
  });

  const lookup = Object.fromEntries(branches.map((branch) => [branch.nodeId, { branchName: branch.branchName, workingDir: branch.workingDir }]));

  return {
    version: SCAFFOLD_VERSION,
    template: options.template,
    generatedAt,
    meta,
    branches,
    lookup,
  };
}
