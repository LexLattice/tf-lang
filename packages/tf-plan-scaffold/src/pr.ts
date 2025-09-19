import { spawn } from "node:child_process";
import { findRepoRoot } from "@tf-lang/utils";
import type { ScaffoldPlan, ScaffoldBranchPlan } from "@tf-lang/tf-plan-scaffold-core";

function sanitizeTitle(input: string): string {
  return input.replace(/[\r\n]+/g, " ").replace(/\s+/g, " ").trim();
}

function renderPrBody(branch: ScaffoldBranchPlan, plan: ScaffoldPlan): string {
  const summary = branch.summary;
  const score = summary.score.total.toFixed(2);
  const risk = summary.score.risk.toFixed(2);
  return [
    `## Plan Node ${branch.nodeId}`,
    `- Template: ${plan.meta.templateName}`,
    `- Score: ${score}`,
    `- Risk: ${risk}`,
    "",
    summary.rationale,
  ].join("\n");
}

async function runGh(args: readonly string[], cwd: string): Promise<void> {
  await new Promise<void>((resolve, reject) => {
    const child = spawn("gh", args, {
      cwd,
      stdio: "inherit",
      shell: false,
    });
    child.on("error", (error) => reject(error));
    child.on("exit", (code) => {
      if (code === 0) {
        resolve();
      } else {
        reject(new Error(`gh ${args.join(" ")} exited with code ${code}`));
      }
    });
  });
}

export interface CreatePrOptions {
  readonly repoRoot?: string;
  readonly openDraft?: boolean;
}

export async function createDraftPullRequests(
  plan: ScaffoldPlan,
  options: CreatePrOptions = {}
): Promise<void> {
  const repoRoot = options.repoRoot ?? findRepoRoot();
  const openDraft = options.openDraft ?? false;
  for (const branch of plan.branches) {
    const title = sanitizeTitle(`T4 ${plan.meta.specId} ${branch.branchSlug}`);
    const body = renderPrBody(branch, plan);
    if (openDraft) {
      await runGh(
        [
          "pr",
          "create",
          "--draft",
          "--title",
          title,
          "--body",
          body,
          "--head",
          branch.branchName,
          "--base",
          plan.meta.baseBranch,
        ],
        repoRoot
      );
    } else {
      process.stdout.write(
        `Draft PR ready for ${branch.branchName}\nTitle: ${title}\nBase: ${plan.meta.baseBranch}\n\n`
      );
    }
  }
}
