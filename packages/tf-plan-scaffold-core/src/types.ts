import type { PlanGraphMeta, PlanNode } from "@tf-lang/tf-plan-core";

export const SCAFFOLD_PLAN_VERSION = "0.1.0" as const;

export type TemplateTarget = "workdir" | "repo" | "ci";

export interface TemplateFileTemplate {
  readonly sourcePath: string;
  readonly target: TemplateTarget;
  readonly scope: "branch" | "global";
  readonly relativePathTemplate: string;
  readonly contentTemplate: string;
}

export interface TemplatePack {
  readonly name: string;
  readonly description: string;
  readonly files: readonly TemplateFileTemplate[];
  readonly packageJsonScripts: Readonly<Record<string, string>>;
}

export interface RenderedFile {
  readonly sourcePath: string;
  readonly target: TemplateTarget;
  readonly path: string;
  readonly contents: string;
  readonly digest: string;
}

export interface PackageJsonUpdate {
  readonly path: string;
  readonly scripts: Readonly<Record<string, string>>;
}

export interface RepoActionCreateBranch {
  readonly type: "create-branch";
  readonly branchName: string;
  readonly baseBranch: string;
}

export type RepoAction = RepoActionCreateBranch;

export interface BranchScoreSummary {
  readonly total: number;
  readonly complexity: number;
  readonly risk: number;
  readonly perf: number;
  readonly devTime: number;
  readonly depsReady: number;
}

export interface BranchSummary {
  readonly component: string;
  readonly choice: string;
  readonly rationale: string;
  readonly score: BranchScoreSummary;
}

export interface ScaffoldBranchPlan {
  readonly nodeId: string;
  readonly branchName: string;
  readonly branchSlug: string;
  readonly worktreePath: string;
  readonly summary: BranchSummary;
  readonly repoActions: readonly RepoAction[];
  readonly files: readonly RenderedFile[];
  readonly packageJsonUpdates: readonly PackageJsonUpdate[];
}

export interface ScaffoldPlanMeta {
  readonly version: string;
  readonly specId: string;
  readonly specHash: string;
  readonly seed: number;
  readonly planVersion: string;
  readonly templateName: string;
  readonly templateHash: string;
  readonly baseBranch: string;
  readonly branchPrefix: string;
  readonly worktreeRoot: string;
  readonly reusableWorkflowPath: string;
  readonly limit: number;
  readonly totalCandidates: number;
  readonly selectedBranches: number;
}

export interface TemplateSummary {
  readonly name: string;
  readonly description: string;
  readonly fileCount: number;
}

export interface GlobalScaffoldActions {
  readonly files: readonly RenderedFile[];
  readonly packageJsonUpdates: readonly PackageJsonUpdate[];
}

export interface ScaffoldPlanIndexEntry {
  readonly nodeId: string;
  readonly branchName: string;
  readonly worktreePath: string;
}

export interface ScaffoldPlan {
  readonly meta: ScaffoldPlanMeta;
  readonly template: TemplateSummary;
  readonly global: GlobalScaffoldActions;
  readonly branches: readonly ScaffoldBranchPlan[];
  readonly index: readonly ScaffoldPlanIndexEntry[];
}

export interface PlanSource {
  readonly nodes: readonly PlanNode[];
  readonly meta: PlanGraphMeta;
}

export interface CreateScaffoldPlanOptions {
  readonly template: TemplatePack;
  readonly limit?: number;
  readonly baseBranch?: string;
  readonly branchPrefix?: string;
  readonly worktreeRoot?: string;
  readonly reusableWorkflowPath?: string;
}

export interface TemplateRenderContext {
  readonly specId: string;
  readonly templateName: string;
  readonly baseBranch: string;
  readonly branchName: string;
  readonly branchSlug: string;
  readonly nodeId: string;
  readonly shortId: string;
}
