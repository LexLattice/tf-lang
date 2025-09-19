import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import { createRequire } from 'node:module';
import Ajv from 'ajv';
import type { ErrorObject } from 'ajv';
import {
  PlanGraph,
  PlanNode,
  Score,
  PLAN_GRAPH_VERSION,
  deepFreeze,
  stableSort,
} from '@tf-lang/tf-plan-core';
import { enumeratePlan, readSpec } from '@tf-lang/tf-plan-enum';
import { scorePlanNode } from '@tf-lang/tf-plan-scoring';

const require = createRequire(import.meta.url);
const planSchema = loadSchema('tf-plan.schema.json');
const branchSchema = loadSchema('tf-branch.schema.json');
const ajv = new Ajv({ allErrors: true, strict: false });
ajv.addSchema(branchSchema, 'tf-branch.schema.json');
const validatePlanGraph = ajv.compile<PlanGraph>(planSchema);
const validatePlanNode = ajv.compile<PlanNode>(branchSchema);

function loadSchema(name: string): Record<string, unknown> {
  const candidates = [
    `../../../schema/${name}`,
    `../../../../schema/${name}`,
  ];
  for (const candidate of candidates) {
    try {
      return require(candidate);
    } catch {
      continue;
    }
  }
  throw new Error(`Unable to load schema ${name}`);
}

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

export function validatePlan(plan: PlanGraph): void {
  if (!validatePlanGraph(plan)) {
    const message =
      validatePlanGraph.errors?.map((error: ErrorObject) => `${error.instancePath} ${error.message}`).join(', ') ?? 'unknown error';
    throw new Error(`Plan graph failed validation: ${message}`);
  }
  plan.nodes.forEach((node) => {
    if (!validatePlanNode(node)) {
      const message =
        validatePlanNode.errors?.map((error: ErrorObject) => `${error.instancePath} ${error.message}`).join(', ') ?? 'unknown error';
      const nodeId = (node as { nodeId?: string }).nodeId ?? '<unknown>';
      throw new Error(`Plan node ${nodeId} failed validation: ${message}`);
    }
  });
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
  validatePlan(parsed);
  return parsed;
}

export async function runEnumerateCommand(args: EnumerateCommandArgs): Promise<PlanGraph> {
  const spec = await readSpec(args.specPath);
  const plan = enumeratePlan(spec, {
    seed: args.seed,
    beamWidth: args.beamWidth,
    maxBranches: args.maxBranches,
  });
  validatePlan(plan);

  const planPath = join(args.outDir, 'plan.json');
  const ndjsonPath = join(args.outDir, 'plan.ndjson');
  await writeJsonFile(planPath, plan);
  await writeNdjson(ndjsonPath, plan.nodes);

  const branchNodes = plan.nodes.filter((node) => node.component.startsWith('branch:'));
  const summary = branchNodes
    .slice(0, 5)
    .map((node, index) => `${index + 1}. ${node.choice} → total ${node.score.total.toFixed(2)}`)
    .join('\n');
  console.log(`Enumerated ${branchNodes.length} branches (seed=${plan.meta.seed}). Top branches:\n${summary}`);

  return plan;
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
