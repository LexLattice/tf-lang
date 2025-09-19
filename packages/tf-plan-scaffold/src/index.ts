import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import {
  PlanGraph,
  PlanNode,
  PLAN_GRAPH_VERSION,
  validateBranch,
  validatePlan,
  parseSpecId,
} from '@tf-lang/tf-plan-core';
import {
  PlanSummaryMeta,
  ScaffoldPlan,
  TemplateKind,
  createScaffoldPlan,
} from '@tf-lang/tf-plan-scaffold-core';

async function ensureDir(filePath: string): Promise<void> {
  await mkdir(filePath, { recursive: true });
}

function parseTemplate(input: string | undefined, fallback: TemplateKind): TemplateKind {
  if (!input) {
    return fallback;
  }
  if (input === 'ts' || input === 'rs' || input === 'dual-stack') {
    return input;
  }
  throw new Error(`Unsupported template '${input}'.`);
}

function parseNumber(input: unknown, fallback: number): number {
  const value = typeof input === 'string' ? Number.parseInt(input, 10) : typeof input === 'number' ? input : fallback;
  if (!Number.isFinite(value) || value <= 0) {
    return fallback;
  }
  return value;
}

async function readNodesFromNdjson(planPath: string): Promise<PlanNode[]> {
  const raw = await readFile(resolve(planPath), 'utf8');
  const lines = raw.trim().length === 0 ? [] : raw.trim().split('\n');
  const nodes: PlanNode[] = lines.map((line) => JSON.parse(line) as PlanNode);
  nodes.forEach((node) => {
    validateBranch(node);
  });
  return nodes;
}

async function readPlanMeta(
  planJsonPath: string | undefined,
  nodes: readonly PlanNode[],
  seedOverride: number,
): Promise<PlanSummaryMeta> {
  if (planJsonPath) {
    const raw = await readFile(resolve(planJsonPath), 'utf8');
    const parsed = validatePlan(JSON.parse(raw) as PlanGraph);
    return parsed.meta;
  }

  const fallbackSeed = Number.isFinite(seedOverride) ? seedOverride : 42;
  const specHash = nodes.length > 0
    ? (() => {
        try {
          return parseSpecId(nodes[0].specId).specHash;
        } catch {
          return 'unknown';
        }
      })()
    : 'unknown';
  return { seed: fallbackSeed, specHash, version: PLAN_GRAPH_VERSION };
}

async function writeJsonFile(outPath: string, value: unknown): Promise<void> {
  await ensureDir(dirname(outPath));
  await writeFile(outPath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
}

export interface GenerateScaffoldArgs {
  readonly planNdjsonPath: string;
  readonly planJsonPath?: string;
  readonly top: number;
  readonly template: TemplateKind;
  readonly outPath: string;
  readonly baseBranch?: string;
  readonly seed: number;
}

export interface ApplyScaffoldArgs {
  readonly indexPath: string;
}

export async function generateScaffold(args: GenerateScaffoldArgs): Promise<ScaffoldPlan> {
  const nodes = await readNodesFromNdjson(args.planNdjsonPath);
  const meta = await readPlanMeta(args.planJsonPath, nodes, args.seed);
  const plan = createScaffoldPlan(nodes, meta, {
    template: args.template,
    top: args.top,
    baseBranch: args.baseBranch,
  });
  await writeJsonFile(args.outPath, plan);
  console.log(`Scaffold dry-run written to ${args.outPath} with ${plan.branches.length} branches.`);
  return plan;
}

export async function applyScaffold(args: ApplyScaffoldArgs): Promise<ScaffoldPlan> {
  const raw = await readFile(resolve(args.indexPath), 'utf8');
  const parsed = JSON.parse(raw) as ScaffoldPlan;
  console.log(`Apply mode is currently a no-op. Review ${args.indexPath} and execute actions manually.`);
  return parsed;
}

export { parseTemplate, parseNumber };
