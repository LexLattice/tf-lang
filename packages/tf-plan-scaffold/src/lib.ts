import { readFile } from "node:fs/promises";
import { createScaffoldPlan, SCAFFOLD_PLAN_VERSION, type ScaffoldPlan } from "@tf-lang/tf-plan-scaffold-core";
import type { CreateScaffoldPlanOptions } from "@tf-lang/tf-plan-scaffold-core";
import { applyScaffoldPlan, type ApplyOptions } from "./apply.js";
import { createDraftPullRequests, type CreatePrOptions } from "./pr.js";
import { formatPlanSummary, writeScaffoldPlan } from "./output.js";
import { loadPlanSource, type LoadPlanOptions } from "./plan.js";
import { loadTemplatePack, type LoadTemplateOptions } from "./template.js";

export interface GenerateOptions {
  readonly planPath: string;
  readonly templateName: string;
  readonly limit?: number;
  readonly baseBranch?: string;
  readonly branchPrefix?: string;
  readonly worktreeRoot?: string;
  readonly reusableWorkflowPath?: string;
  readonly planOptions?: LoadPlanOptions;
  readonly templateOptions?: LoadTemplateOptions;
}

export async function generateScaffoldPlan(options: GenerateOptions): Promise<ScaffoldPlan> {
  const source = await loadPlanSource(options.planPath, options.planOptions);
  const template = await loadTemplatePack(options.templateName, options.templateOptions);
  const planOptions: CreateScaffoldPlanOptions = {
    template,
    limit: options.limit,
    baseBranch: options.baseBranch,
    branchPrefix: options.branchPrefix,
    worktreeRoot: options.worktreeRoot,
    reusableWorkflowPath: options.reusableWorkflowPath,
  };
  return createScaffoldPlan(source, planOptions);
}

export async function readScaffoldPlan(planPath: string): Promise<ScaffoldPlan> {
  const raw = await readFile(planPath, "utf-8");
  const plan = JSON.parse(raw) as ScaffoldPlan;
  if (!plan.meta || plan.meta.version !== SCAFFOLD_PLAN_VERSION) {
    throw new Error(`unsupported scaffold plan version in ${planPath}`);
  }
  return plan;
}

export {
  applyScaffoldPlan,
  type ApplyOptions,
  createDraftPullRequests,
  type CreatePrOptions,
  formatPlanSummary,
  loadPlanSource,
  loadTemplatePack,
  type LoadPlanOptions,
  type LoadTemplateOptions,
  writeScaffoldPlan,
};
