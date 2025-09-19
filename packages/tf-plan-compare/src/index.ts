import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import { PlanNode, validateBranch, validateCompare } from '@tf-lang/tf-plan-core';
import { ScaffoldPlan } from '@tf-lang/tf-plan-scaffold-core';
import { buildCompareReport } from '@tf-lang/tf-plan-compare-core';
import type { CompareReport } from '@tf-lang/tf-plan-compare-core';
import { renderHtml, renderMarkdown } from '@tf-lang/tf-plan-compare-render';

async function ensureDir(filePath: string): Promise<void> {
  await mkdir(filePath, { recursive: true });
}

async function readNdjson(planPath: string): Promise<PlanNode[]> {
  const raw = await readFile(resolve(planPath), 'utf8');
  const lines = raw.trim().length === 0 ? [] : raw.trim().split('\n');
  return lines.map((line, index) => {
    try {
      const parsed = JSON.parse(line) as unknown;
      return validateBranch(parsed);
    } catch (error) {
      throw new Error(`Invalid plan node at line ${index + 1} in ${planPath}: ${(error as Error).message}`);
    }
  });
}

async function readScaffold(indexPath: string): Promise<ScaffoldPlan> {
  const raw = await readFile(resolve(indexPath), 'utf8');
  return JSON.parse(raw) as ScaffoldPlan;
}

export interface CompareArgs {
  readonly planNdjsonPath: string;
  readonly scaffoldPath: string;
  readonly outDir: string;
  readonly seed: number;
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
  const report = buildCompareReport(nodes, scaffold, { seed: args.seed });
  validateCompare<CompareReport>(report);
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
