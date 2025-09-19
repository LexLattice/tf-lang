import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";
import { canonicalJson } from "@tf-lang/utils";
import type { ScaffoldPlan } from "@tf-lang/tf-plan-scaffold-core";

export async function writeScaffoldPlan(plan: ScaffoldPlan, outPath: string): Promise<void> {
  await mkdir(path.dirname(outPath), { recursive: true });
  await writeFile(outPath, canonicalJson(plan), "utf-8");
}

function formatBranchLine(plan: ScaffoldPlan, index: number): string {
  const branch = plan.branches[index];
  const score = branch.summary.score.total.toFixed(2);
  const risk = branch.summary.score.risk.toFixed(2);
  return `  - ${branch.branchName} (node ${branch.nodeId}, score ${score}, risk ${risk})`;
}

export function formatPlanSummary(plan: ScaffoldPlan): string {
  const header = `Scaffold plan for spec ${plan.meta.specId} using template ${plan.meta.templateName}`;
  const branchLines = plan.branches.map((_branch, index) => formatBranchLine(plan, index));
  return [header, `Base branch: ${plan.meta.baseBranch}`, `Branches (${plan.branches.length}):`, ...branchLines].join("\n");
}
