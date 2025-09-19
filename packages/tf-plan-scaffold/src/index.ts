import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import { createRequire } from 'node:module';
import Ajv from 'ajv';
import type { ErrorObject } from 'ajv';
import {
  PlanGraph,
  PlanNode,
  PLAN_GRAPH_VERSION,
} from '@tf-lang/tf-plan-core';
import {
  PlanSummaryMeta,
  ScaffoldPlan,
  TemplateKind,
  createScaffoldPlan,
} from '@tf-lang/tf-plan-scaffold-core';

const require = createRequire(import.meta.url);
const planSchema = loadSchema('tf-plan.schema.json');
const branchSchema = loadSchema('tf-branch.schema.json');
const ajv = new Ajv({ allErrors: true, strict: false });
ajv.addSchema(branchSchema, 'tf-branch.schema.json');
const validateNode = ajv.compile<PlanNode>(branchSchema);
const validatePlanGraph = ajv.compile<PlanGraph>(planSchema);

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
    if (!validateNode(node)) {
      const message =
        validateNode.errors?.map((error: ErrorObject) => `${error.instancePath} ${error.message}`).join(', ') ?? 'unknown error';
      throw new Error(`Invalid plan node in NDJSON: ${message}`);
    }
  });
  return nodes;
}

async function readPlanMeta(planJsonPath: string | undefined, nodes: readonly PlanNode[]): Promise<PlanSummaryMeta> {
  if (planJsonPath) {
    const raw = await readFile(resolve(planJsonPath), 'utf8');
    const parsed = JSON.parse(raw) as PlanGraph;
    if (!validatePlanGraph(parsed)) {
      const message =
        validatePlanGraph.errors?.map((error: ErrorObject) => `${error.instancePath} ${error.message}`).join(', ') ?? 'unknown error';
      throw new Error(`Plan graph validation failed: ${message}`);
    }
    return parsed.meta;
  }

  const fallbackSeed = 42;
  const specHash = nodes.length > 0 ? nodes[0].specId.split(':')[1] ?? 'unknown' : 'unknown';
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
}

export interface ApplyScaffoldArgs {
  readonly indexPath: string;
}

export async function generateScaffold(args: GenerateScaffoldArgs): Promise<ScaffoldPlan> {
  const nodes = await readNodesFromNdjson(args.planNdjsonPath);
  const meta = await readPlanMeta(args.planJsonPath, nodes);
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
