import { readFile } from 'node:fs/promises';
import { resolve as resolvePath } from 'node:path';
import Ajv from 'ajv';
import type { ErrorObject } from 'ajv';
import tfSpecSchema from '../../../schema/tf-spec.schema.json' with { type: 'json' };
import {
  PLAN_GRAPH_VERSION,
  PlanEdge,
  PlanGraph,
  PlanNode,
  RepoSignals,
  Score,
  deepFreeze,
  hashObject,
  seedRng,
  stableId,
  stableSort,
} from '@tf-lang/tf-plan-core';
import { scorePlanNode } from '@tf-lang/tf-plan-scoring';

const ajv = new Ajv({ allErrors: true, strict: false });
const validateSpec = ajv.compile(tfSpecSchema);

export interface TfSpecStep {
  readonly op: 'copy' | 'create_vm' | 'create_network';
  readonly params: Record<string, unknown>;
}

export interface TfSpec {
  readonly version: string;
  readonly name: string;
  readonly steps: readonly TfSpecStep[];
}

export interface EnumerateOptions {
  readonly seed?: number;
  readonly beamWidth?: number;
  readonly maxBranches?: number;
  readonly includeChoices?: Readonly<Record<string, readonly string[]>>;
  readonly excludeChoices?: Readonly<Record<string, readonly string[]>>;
  readonly repoSignals?: RepoSignals;
}

interface ComponentChoice {
  readonly choice: string;
  readonly rationale: string;
}

interface ComponentPlan {
  readonly componentId: string;
  readonly label: string;
  readonly choice: ComponentChoice;
  readonly node: PlanNode;
}

const choiceLibrary: Record<TfSpecStep['op'], readonly ComponentChoice[]> = {
  copy: [
    {
      choice: 'managed rsync pipeline',
      rationale: 'Leverages existing rsync workers with checksum validation and resumable syncs.',
    },
    {
      choice: 'object storage replication',
      rationale: 'Pushes payloads to durable object storage with lifecycle policies and versioning.',
    },
    {
      choice: 'delta snapshot streaming',
      rationale: 'Streams block-level snapshots incrementally to reduce data transfer volume.',
    },
  ],
  create_vm: [
    {
      choice: 'standard compute pool',
      rationale: 'Uses balanced compute instances with reserved capacity for predictable throughput.',
    },
    {
      choice: 'spot auto-healing cluster',
      rationale: 'Optimises cost with spot nodes while health checks replace evicted instances quickly.',
    },
    {
      choice: 'gpu accelerated workers',
      rationale: 'Accelerates compute-heavy workloads with managed GPU nodes and tuned drivers.',
    },
  ],
  create_network: [
    {
      choice: 'segmented service mesh',
      rationale: 'Creates layered subnets with strict firewall policies and service discovery.',
    },
    {
      choice: 'flat network with security groups',
      rationale: 'Keeps topology simple with security groups guarding ingress and egress.',
    },
    {
      choice: 'zero trust overlay',
      rationale: 'Applies identity-aware proxies and policy enforcement at the edge.',
    },
  ],
};

function comparePlanNodes(left: PlanNode, right: PlanNode): number {
  const totalDiff = right.score.total - left.score.total;
  if (totalDiff !== 0) {
    return totalDiff;
  }
  const riskDiff = left.score.risk - right.score.risk;
  if (riskDiff !== 0) {
    return riskDiff;
  }
  return left.nodeId.localeCompare(right.nodeId);
}

function assertValidSpec(spec: TfSpec): void {
  const result = validateSpec(spec);
  if (!result) {
    const message =
      validateSpec.errors?.map((error: ErrorObject) => `${error.instancePath} ${error.message}`).join(', ') ?? 'unknown error';
    throw new Error(`Invalid tf-spec: ${message}`);
  }
}

function isChoiceAllowed(componentId: string, choice: ComponentChoice, options: EnumerateOptions): boolean {
  const { includeChoices, excludeChoices } = options;
  if (includeChoices && includeChoices[componentId] && !includeChoices[componentId]?.includes(choice.choice)) {
    return false;
  }
  if (excludeChoices && excludeChoices[componentId] && excludeChoices[componentId]?.includes(choice.choice)) {
    return false;
  }
  return true;
}

function buildComponentPlan(
  componentId: string,
  label: string,
  choice: ComponentChoice,
  specId: string,
  seed: number,
  version: string,
  repoSignals: RepoSignals,
): PlanNode {
  const nodeIdentity = stableId({
    scope: 'component',
    specId,
    component: componentId,
    choice: choice.choice,
    seed,
    version,
  });

  const score = scorePlanNode({ component: componentId, choice: choice.choice, seed, repoSignals });

  return {
    nodeId: nodeIdentity.full,
    specId,
    component: componentId,
    choice: choice.choice,
    deps: [],
    rationale: `${label}: ${choice.rationale}`,
    score,
  };
}

function round(value: number, precision = 3): number {
  const factor = 10 ** precision;
  return Math.round(value * factor) / factor;
}

function aggregateScore(nodes: readonly PlanNode[]): Score {
  if (nodes.length === 0) {
    return {
      total: 0,
      complexity: 0,
      risk: 0,
      perf: 0,
      devTime: 0,
      depsReady: 0,
      explain: ['No component nodes were provided.'],
    };
  }

  const totals = nodes.reduce(
    (acc, node) => {
      acc.total += node.score.total;
      acc.complexity += node.score.complexity;
      acc.risk += node.score.risk;
      acc.perf += node.score.perf;
      acc.devTime += node.score.devTime;
      acc.depsReady += node.score.depsReady;
      acc.explain.push(`${node.component} via ${node.choice} → total ${node.score.total.toFixed(2)}`);
      return acc;
    },
    {
      total: 0,
      complexity: 0,
      risk: 0,
      perf: 0,
      devTime: 0,
      depsReady: 0,
      explain: [] as string[],
    },
  );

  const count = nodes.length;
  const summary = `Aggregated from ${count} components.`;
  totals.explain.push(summary);

  return {
    total: round(totals.total / count),
    complexity: round(totals.complexity / count),
    risk: round(totals.risk / count),
    perf: round(totals.perf / count),
    devTime: round(totals.devTime / count),
    depsReady: round(totals.depsReady / count),
    explain: totals.explain,
  };
}

function buildBranchNode(
  specId: string,
  branchLabel: string,
  components: readonly ComponentPlan[],
  seed: number,
  version: string,
): PlanNode {
  const choiceSummary = components.map((component) => `${component.label}=${component.choice.choice}`).join('; ');
  const nodeIdentity = stableId({
    scope: 'branch',
    specId,
    component: branchLabel,
    choice: choiceSummary,
    seed,
    version,
  });

  const componentNodes = components.map((component) => component.node);
  const score = aggregateScore(componentNodes);
  const rationale = `Combines ${components.map((component) => `${component.label} via ${component.choice.choice}`).join(', ')}.`;

  return {
    nodeId: nodeIdentity.full,
    specId,
    component: branchLabel,
    choice: choiceSummary,
    deps: componentNodes.map((node) => node.nodeId),
    rationale,
    score,
  };
}

function enumerateComponentPlans(
  spec: TfSpec,
  options: EnumerateOptions,
  specId: string,
  seed: number,
  version: string,
): ComponentPlan[] {
  const plans: ComponentPlan[] = [];
  const repoSignals = options.repoSignals ?? {};

  spec.steps.forEach((step, index) => {
    const componentId = `${step.op}:${index}`;
    const label = `${step.op}#${index + 1}`;
    const library = choiceLibrary[step.op];

    library.forEach((choice) => {
      if (!isChoiceAllowed(componentId, choice, options)) {
        return;
      }
      const node = buildComponentPlan(componentId, label, choice, specId, seed, version, repoSignals);
      plans.push({ componentId, label, choice, node });
    });
  });

  return plans;
}

function groupByComponent(plans: readonly ComponentPlan[]): Map<string, ComponentPlan[]> {
  const map = new Map<string, ComponentPlan[]>();
  plans.forEach((plan) => {
    const existing = map.get(plan.componentId);
    if (existing) {
      existing.push(plan);
    } else {
      map.set(plan.componentId, [plan]);
    }
  });
  return map;
}

function enumerateBranches(
  componentsById: Map<string, ComponentPlan[]>,
  specId: string,
  seed: number,
  version: string,
  options: EnumerateOptions,
): PlanNode[] {
  const componentIds = [...componentsById.keys()].sort();
  const branchLabel = `branch:${specId}`;
  const branches: PlanNode[] = [];
  const rng = seedRng(seed);

  const explore = (index: number, selected: ComponentPlan[]) => {
    if (index === componentIds.length) {
      branches.push(buildBranchNode(specId, branchLabel, selected, seed, version));
      return;
    }
    const componentId = componentIds[index];
    const optionsForComponent = componentsById.get(componentId) ?? [];
    const sortedOptions = stableSort(optionsForComponent, (left, right) => comparePlanNodes(left.node, right.node));

    const beamWidth = options.beamWidth ?? sortedOptions.length;
    const limited = sortedOptions.slice(0, Math.max(0, beamWidth));

    limited.forEach((choice) => {
      explore(index + 1, [...selected, choice]);
    });
  };

  explore(0, []);
  const sortedBranches = stableSort(branches, comparePlanNodes);

  const maxBranches = options.maxBranches ?? sortedBranches.length;
  const chosen = sortedBranches.slice(0, Math.max(0, maxBranches));

  // Shuffle deterministically to avoid bias when totals tie.
  const decorated = chosen.map((branch) => ({ branch, key: rng.next() }));
  decorated.sort((a, b) => {
    if (a.branch.score.total !== b.branch.score.total) {
      return b.branch.score.total - a.branch.score.total;
    }
    if (a.branch.score.risk !== b.branch.score.risk) {
      return a.branch.score.risk - b.branch.score.risk;
    }
    return a.key - b.key;
  });

  return decorated.map((entry) => entry.branch);
}

export interface EnumeratePlanResult {
  readonly plan: PlanGraph;
  readonly branchCount: number;
}

export async function readSpec(specPath: string): Promise<TfSpec> {
  const absolute = resolvePath(specPath);
  const raw = await readFile(absolute, 'utf8');
  const parsed = JSON.parse(raw) as TfSpec;
  assertValidSpec(parsed);
  return parsed;
}

export function enumeratePlan(spec: TfSpec, options: EnumerateOptions = {}): PlanGraph {
  assertValidSpec(spec);
  const seed = options.seed ?? 42;
  const specHash = hashObject(spec);
  const specId = `${spec.name}:${specHash.slice(0, 8)}`;
  const componentPlans = enumerateComponentPlans(spec, options, specId, seed, PLAN_GRAPH_VERSION);
  if (componentPlans.length === 0) {
    throw new Error('No component plans generated. Adjust constraints to allow at least one choice per component.');
  }

  const componentsById = groupByComponent(componentPlans);
  const branchNodes = enumerateBranches(componentsById, specId, seed, PLAN_GRAPH_VERSION, options);
  if (branchNodes.length === 0) {
    throw new Error('Enumeration finished without branch nodes. Relax beam or maxBranches constraints.');
  }

  const branchIds = new Set(branchNodes.map((branch) => branch.nodeId));
  const nodes: PlanNode[] = [...componentPlans.map((plan) => plan.node), ...branchNodes];
  const sortedNodes = stableSort(nodes, comparePlanNodes);

  const edges: PlanEdge[] = branchNodes.flatMap((branch) =>
    branch.deps.map((dependency) => ({ from: branch.nodeId, to: dependency, kind: 'depends' as const })),
  );

  const planGraph: PlanGraph = {
    version: PLAN_GRAPH_VERSION,
    nodes: sortedNodes,
    edges,
    meta: {
      seed,
      specHash,
      version: PLAN_GRAPH_VERSION,
    },
  };

  return deepFreeze(planGraph);
}
