import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import {
  PlanGraph,
  PlanNode,
  Score,
  PLAN_GRAPH_VERSION,
  deepFreeze,
  stableSort,
  validatePlan,
} from '@tf-lang/tf-plan-core';
import { enumeratePlan, readSpec } from '@tf-lang/tf-plan-enum';
import { scorePlanNode } from '@tf-lang/tf-plan-scoring';

function asNumber(value: unknown, fallback: number): number {
  const parsed = typeof value === 'string' ? Number.parseFloat(value) : typeof value === 'number' ? value : fallback;
  if (!Number.isFinite(parsed)) {
    return fallback;
  }
  return parsed;
}

async function ensureDir(filePath: string): Promise<void> {
  await mkdir(filePath, { recursive: true });
}

export interface EnumerateCommandArgs {
  readonly specPath: string;
  readonly seed: number;
  readonly beamWidth?: number;
  readonly maxBranches?: number;
  readonly outDir: string;
}

export interface ScoreCommandArgs {
  readonly planPath: string;
  readonly outPath: string;
  readonly seed?: number;
}

export interface ExportCommandArgs {
  readonly planPath: string;
  readonly ndjsonPath: string;
}

function round(value: number, precision = 3): number {
  const factor = 10 ** precision;
  return Math.round(value * factor) / factor;
}

function aggregateScores(nodes: readonly PlanNode[]): Score {
  if (nodes.length === 0) {
    return {
      total: 0,
      complexity: 0,
      risk: 0,
      perf: 0,
      devTime: 0,
      depsReady: 0,
      explain: ['No dependency scores provided.'],
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
      acc.explain.push(`${node.component} via ${node.choice} scored ${node.score.total.toFixed(2)}`);
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
  totals.explain.push(`Aggregate of ${count} nodes.`);
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

function rescorePlan(plan: PlanGraph, seedOverride?: number): PlanGraph {
  const seed = seedOverride ?? plan.meta.seed;
  const nodeMap = new Map(plan.nodes.map((node) => [node.nodeId, node] as const));
  const rescoredNodes = plan.nodes.map((node) => {
    if (node.deps.length === 0) {
      const score = scorePlanNode({ component: node.component, choice: node.choice, seed });
      return { ...node, score } satisfies PlanNode;
    }
    const dependencies = node.deps.map((dep) => nodeMap.get(dep)).filter((dep): dep is PlanNode => dep !== undefined);
    const score = aggregateScores(dependencies);
    return { ...node, score } satisfies PlanNode;
  });

  const sorted = stableSort(rescoredNodes, (left, right) => {
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

  const updated: PlanGraph = {
    ...plan,
    nodes: sorted,
    meta: {
      ...plan.meta,
      seed,
    },
  };

  return deepFreeze(updated);
}

async function writeJsonFile(filePath: string, value: unknown): Promise<void> {
  await ensureDir(dirname(filePath));
  const content = `${JSON.stringify(value, null, 2)}\n`;
  await writeFile(filePath, content, 'utf8');
}

async function writeNdjson(filePath: string, nodes: readonly PlanNode[]): Promise<void> {
  await ensureDir(dirname(filePath));
  const lines = nodes.map((node) => JSON.stringify(node));
  const content = `${lines.join('\n')}\n`;
  await writeFile(filePath, content, 'utf8');
}

async function readPlan(planPath: string): Promise<PlanGraph> {
  const absolute = resolve(planPath);
  const raw = await readFile(absolute, 'utf8');
  const parsed = JSON.parse(raw) as PlanGraph;
  return validatePlan(parsed);
}

export async function runEnumerateCommand(args: EnumerateCommandArgs): Promise<PlanGraph> {
  const spec = await readSpec(args.specPath);
  const plan = enumeratePlan(spec, {
    seed: args.seed,
    beamWidth: args.beamWidth ?? 3,
    maxBranches: args.maxBranches,
  });
  const validated = validatePlan(plan);

  const planPath = join(args.outDir, 'plan.json');
  const ndjsonPath = join(args.outDir, 'plan.ndjson');
  await writeJsonFile(planPath, validated);
  await writeNdjson(ndjsonPath, validated.nodes);

  const branchNodes = validated.nodes.filter((node) => node.component.startsWith('branch:'));
  const summary = branchNodes
    .slice(0, 5)
    .map((node, index) => `${index + 1}. ${node.choice} → total ${node.score.total.toFixed(2)}`)
    .join('\n');
  console.log(`Enumerated ${branchNodes.length} branches (seed=${validated.meta.seed}). Top branches:\n${summary}`);

  return validated;
}

export async function runScoreCommand(args: ScoreCommandArgs): Promise<PlanGraph> {
  const plan = await readPlan(args.planPath);
  const rescored = rescorePlan(plan, args.seed);
  await writeJsonFile(args.outPath, rescored);
  console.log(`Re-scored plan graph written to ${args.outPath}`);
  return rescored;
}

export async function runExportCommand(args: ExportCommandArgs): Promise<void> {
  const plan = await readPlan(args.planPath);
  await writeNdjson(args.ndjsonPath, plan.nodes);
  console.log(`Exported ${plan.nodes.length} nodes to ${args.ndjsonPath}`);
}

export function parseNumberOption(value: unknown, fallback: number): number {
  return asNumber(value, fallback);
}

export { PLAN_GRAPH_VERSION } from '@tf-lang/tf-plan-core';
