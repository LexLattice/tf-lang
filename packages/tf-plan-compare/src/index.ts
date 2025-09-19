import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import { createRequire } from 'node:module';
import Ajv from 'ajv';
import type { ErrorObject } from 'ajv';
import { PlanNode } from '@tf-lang/tf-plan-core';
import { ScaffoldPlan } from '@tf-lang/tf-plan-scaffold-core';
import { buildCompareReport } from '@tf-lang/tf-plan-compare-core';
import type { CompareReport } from '@tf-lang/tf-plan-compare-core';
import { renderHtml, renderMarkdown } from '@tf-lang/tf-plan-compare-render';

const require = createRequire(import.meta.url);
const branchSchema = loadSchema('tf-branch.schema.json');
const compareSchema = loadSchema('tf-compare.schema.json');
const ajv = new Ajv({ allErrors: true, strict: false });
ajv.addSchema(branchSchema, 'tf-branch.schema.json');
const validateNode = ajv.compile<PlanNode>(branchSchema);
const validateCompare = ajv.compile<CompareReport>(compareSchema);

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

async function readNdjson(planPath: string): Promise<PlanNode[]> {
  const raw = await readFile(resolve(planPath), 'utf8');
  const lines = raw.trim().length === 0 ? [] : raw.trim().split('\n');
  const nodes = lines.map((line) => JSON.parse(line) as PlanNode);
  nodes.forEach((node) => {
    if (!validateNode(node)) {
      const message =
        validateNode.errors?.map((error: ErrorObject) => `${error.instancePath} ${error.message}`).join(', ') ?? 'unknown error';
      throw new Error(`Invalid plan node in ${planPath}: ${message}`);
    }
  });
  return nodes;
}

async function readScaffold(indexPath: string): Promise<ScaffoldPlan> {
  const raw = await readFile(resolve(indexPath), 'utf8');
  return JSON.parse(raw) as ScaffoldPlan;
}

export interface CompareArgs {
  readonly planNdjsonPath: string;
  readonly scaffoldPath: string;
  readonly outDir: string;
}

export interface CompareOutputs {
  readonly report: ReturnType<typeof buildCompareReport>;
  readonly jsonPath: string;
  readonly markdownPath: string;
  readonly htmlPath: string;
}

export async function generateComparison(args: CompareArgs): Promise<CompareOutputs> {
  const nodes = await readNdjson(args.planNdjsonPath);
  const scaffold = await readScaffold(args.scaffoldPath);
  const report = buildCompareReport(nodes, scaffold);
  if (!validateCompare(report)) {
    const message = validateCompare.errors?.map((error) => `${error.instancePath} ${error.message}`).join(', ') ?? 'unknown error';
    throw new Error(`Generated report failed validation: ${message}`);
  }
  const jsonPath = join(args.outDir, 'report.json');
  const markdownPath = join(args.outDir, 'report.md');
  const htmlPath = join(args.outDir, 'index.html');
  await ensureDir(args.outDir);
  await writeFile(jsonPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8');
  await writeFile(markdownPath, `${renderMarkdown(report)}\n`, 'utf8');
  await writeFile(htmlPath, `${renderHtml(report)}\n`, 'utf8');
  console.log(`Comparison report written to ${args.outDir}`);
  return { report, jsonPath, markdownPath, htmlPath };
}
