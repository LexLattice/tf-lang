#!/usr/bin/env node
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import Ajv from 'ajv';
import planSchema from '../../../schema/tf-plan.schema.json' with { type: "json" };
import { enumeratePlanGraph } from '@tf-lang/tf-plan-enum';
import type { PlanGraph, PlanNode } from '@tf-lang/tf-plan-core';
import { createScore, stableSort } from '@tf-lang/tf-plan-core';
import { scorePlanNode } from '@tf-lang/tf-plan-scoring';

const ajv = new Ajv({ strict: false, allErrors: true });
const validatePlan = ajv.compile(planSchema as object);

interface ParsedArgs {
  readonly command: string;
  readonly options: Record<string, string | boolean>;
  readonly extras: readonly string[];
}

function parseArgs(argv: readonly string[]): ParsedArgs {
  const [, , command, ...rest] = argv;
  if (!command) {
    return { command: 'help', options: {}, extras: [] };
  }
  const options: Record<string, string | boolean> = {};
  const extras: string[] = [];
  for (let index = 0; index < rest.length; index += 1) {
    const token = rest[index];
    if (token.startsWith('--')) {
      const key = token.slice(2);
      const next = rest[index + 1];
      if (!next || next.startsWith('--')) {
        options[key] = true;
      } else {
        options[key] = next;
        index += 1;
      }
    } else {
      extras.push(token);
    }
  }
  return { command, options, extras };
}

async function readJson(filePath: string): Promise<unknown> {
  const data = await readFile(filePath, 'utf-8');
  return JSON.parse(data);
}

async function writeJson(filePath: string, value: unknown) {
  await mkdir(dirname(filePath), { recursive: true });
  const json = JSON.stringify(value, null, 2);
  await writeFile(filePath, `${json}\n`, 'utf-8');
}

function ensurePlan(plan: unknown): PlanGraph {
  if (!validatePlan(plan)) {
    const errors = validatePlan.errors?.map((error) => `${error.instancePath} ${error.message}`).join('; ');
    throw new Error(`Plan failed validation: ${errors ?? 'unknown error'}`);
  }
  return plan as PlanGraph;
}

function parseNumberOption(value: string | boolean | undefined, defaultValue: number): number {
  if (value === undefined) {
    return defaultValue;
  }
  if (typeof value === 'boolean') {
    return defaultValue;
  }
  const parsed = Number.parseInt(value, 10);
  if (Number.isNaN(parsed)) {
    return defaultValue;
  }
  return parsed;
}

function parseChoiceSummary(summary: string): { component: string; choice: string }[] {
  if (!summary) {
    return [];
  }
  return summary.split(', ').map((entry) => {
    const [component, choice] = entry.split('=');
    return { component, choice };
  });
}

function rescoreNode(node: PlanNode): PlanNode {
  const selections = parseChoiceSummary(node.choice);
  const explain: string[] = [];
  let complexity = 0;
  let risk = 0;
  let perf = 0;
  let devTime = 0;
  let depsReady = 0;

  for (const selection of selections) {
    const score = scorePlanNode({ component: selection.component, choice: selection.choice });
    explain.push(`${selection.component}: ${score.explain.join('; ')}`);
    complexity += score.complexity;
    risk += score.risk;
    perf += score.perf;
    devTime += score.devTime;
    depsReady += score.depsReady;
  }

  const updated = createScore({
    complexity,
    risk,
    perf,
    devTime,
    depsReady,
    explain,
  });

  return {
    ...node,
    score: updated,
  };
}

async function handleEnumerate(options: Record<string, string | boolean>) {
  const specPath = options.spec;
  if (typeof specPath !== 'string') {
    throw new Error('Missing --spec <path>');
  }
  const seed = parseNumberOption(options.seed, 42);
  const beamWidth = parseNumberOption(options.beam ?? options.beamWidth, 0);
  const outDir = typeof options.out === 'string' ? options.out : 'out/t4/plan';
  const spec = await readJson(specPath);
  const graph = enumeratePlanGraph(spec, { seed, beamWidth: beamWidth > 0 ? beamWidth : undefined });
  ensurePlan(graph);
  const planPath = resolve(outDir, 'plan.json');
  await writeJson(planPath, graph);
  const ndjsonPath = resolve(outDir, 'plan.ndjson');
  const lines = graph.nodes.map((node) => JSON.stringify(node));
  await mkdir(dirname(ndjsonPath), { recursive: true });
  await writeFile(ndjsonPath, `${lines.join('\n')}\n`, 'utf-8');
  process.stdout.write(`Enumerated ${graph.nodes.length} plan nodes → ${planPath}\n`);
}

async function handleScore(options: Record<string, string | boolean>) {
  const planPath = options.plan;
  if (typeof planPath !== 'string') {
    throw new Error('Missing --plan <path>');
  }
  const outPath = typeof options.out === 'string' ? options.out : resolve(dirname(planPath), 'plan.scored.json');
  const plan = ensurePlan(await readJson(planPath));
  const rescoredNodes = plan.nodes.map((node) => rescoreNode(node));
  const sorted = stableSort(rescoredNodes, (a, b) => {
    if (a.score.total !== b.score.total) {
      return b.score.total - a.score.total;
    }
    if (a.score.risk !== b.score.risk) {
      return a.score.risk - b.score.risk;
    }
    return a.nodeId.localeCompare(b.nodeId);
  });
  const updated: PlanGraph = {
    ...plan,
    nodes: sorted,
  };
  await writeJson(outPath, updated);
  process.stdout.write(`Rescored ${sorted.length} plan nodes → ${outPath}\n`);
}

async function handleExport(options: Record<string, string | boolean>) {
  const planPath = options.plan;
  const ndjsonPath = options.ndjson;
  if (typeof planPath !== 'string') {
    throw new Error('Missing --plan <path>');
  }
  if (typeof ndjsonPath !== 'string') {
    throw new Error('Missing --ndjson <path>');
  }
  const plan = ensurePlan(await readJson(planPath));
  const lines = plan.nodes.map((node) => JSON.stringify(node));
  await mkdir(dirname(ndjsonPath), { recursive: true });
  await writeFile(ndjsonPath, `${lines.join('\n')}\n`, 'utf-8');
  process.stdout.write(`Exported plan to ${ndjsonPath}\n`);
}

function printHelp() {
  process.stdout.write(`tf-plan commands:\n`);
  process.stdout.write(`  enumerate --spec <path> [--seed <n>] [--beam <k>] [--out <dir>]\n`);
  process.stdout.write(`  score --plan <path> [--out <path>]\n`);
  process.stdout.write(`  export --plan <path> --ndjson <path>\n`);
}

async function main() {
  try {
    const parsed = parseArgs(process.argv);
    switch (parsed.command) {
      case 'enumerate':
        await handleEnumerate(parsed.options);
        break;
      case 'score':
        await handleScore(parsed.options);
        break;
      case 'export':
        await handleExport(parsed.options);
        break;
      default:
        printHelp();
        break;
    }
  } catch (error) {
    process.stderr.write(`Error: ${(error as Error).message}\n`);
    process.exitCode = 1;
  }
}

void main();
