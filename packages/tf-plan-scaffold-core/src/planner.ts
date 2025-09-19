import path from "node:path";
import {
  hashObject,
  hashString,
  shortId,
  stableSort,
  type PlanNode,
} from "@tf-lang/tf-plan-core";
import type {
  BranchSummary,
  CreateScaffoldPlanOptions,
  PlanSource,
  RenderedFile,
  ScaffoldBranchPlan,
  ScaffoldPlan,
  ScaffoldPlanIndexEntry,
  TemplateFileTemplate,
  TemplatePack,
  TemplateSummary,
} from "./types.js";
import { PackageJsonUpdate, RepoAction, SCAFFOLD_PLAN_VERSION } from "./types.js";

const DEFAULT_LIMIT = 3;
const DEFAULT_BASE_BRANCH = "main";
const DEFAULT_REUSABLE_WORKFLOW_PATH = ".github/workflows/reusable-tf-check.yml";

const SAFE_SEGMENT = /[^a-z0-9]+/g;

function comparePlanNodes(a: PlanNode, b: PlanNode): number {
  const totalDiff = b.score.total - a.score.total;
  if (Math.abs(totalDiff) > 1e-6) {
    return totalDiff > 0 ? 1 : -1;
  }
  const riskDiff = a.score.risk - b.score.risk;
  if (Math.abs(riskDiff) > 1e-6) {
    return riskDiff > 0 ? 1 : -1;
  }
  return a.nodeId.localeCompare(b.nodeId);
}

function sanitizeSegment(input: string): string {
  const lowered = input.toLowerCase();
  const replaced = lowered.replace(SAFE_SEGMENT, "-");
  const trimmed = replaced.replace(/^-+/, "").replace(/-+$/, "");
  return trimmed || "x";
}

function sanitizePathSegments(input: string): string {
  const segments = input
    .split(/[\\/]+/)
    .map((segment) => segment.trim())
    .filter((segment) => segment.length > 0)
    .map(sanitizeSegment);
  return segments.join("/");
}

function buildChoiceSlug(node: PlanNode): string {
  const parts = node.choice.split("|");
  const segments = parts.map((entry) => {
    const [rawKey, rawValue] = entry.split("=", 2);
    if (rawValue) {
      return `${sanitizeSegment(rawKey)}-${sanitizeSegment(rawValue)}`;
    }
    return sanitizeSegment(entry);
  });
  const joined = segments.filter(Boolean).join("-");
  return joined || sanitizeSegment(node.component);
}

function ensureNoParentTraversal(renderedPath: string, label: string): string {
  if (renderedPath.startsWith("/")) {
    throw new Error(`${label} may not be absolute: ${renderedPath}`);
  }
  const normalized = path.posix.normalize(renderedPath);
  if (normalized === ".." || normalized.startsWith("../") || normalized.includes("/../")) {
    throw new Error(`${label} may not traverse parents: ${renderedPath}`);
  }
  return normalized;
}

function renderTemplateString(template: string, context: Record<string, string>, label: string): string {
  const rendered = template.replace(/{{\s*([a-zA-Z0-9_]+)\s*}}/g, (_match, key: string) => {
    if (!(key in context)) {
      throw new Error(`${label} references unknown placeholder ${key}`);
    }
    return context[key];
  });
  const leftover = rendered.match(/{{\s*[a-zA-Z0-9_]+\s*}}/);
  if (leftover) {
    throw new Error(`${label} has unresolved placeholder ${leftover[0]}`);
  }
  return rendered;
}

function renderTemplateFile(
  file: TemplateFileTemplate,
  context: Record<string, string>
): RenderedFile {
  const renderedPath = renderTemplateString(
    file.relativePathTemplate,
    context,
    `template path ${file.sourcePath}`
  );
  const safePath = ensureNoParentTraversal(renderedPath, `template path ${file.sourcePath}`);
  const renderedContent = renderTemplateString(
    file.contentTemplate,
    context,
    `template content ${file.sourcePath}`
  );
  const digest = hashString(renderedContent);
  return {
    sourcePath: file.sourcePath,
    target: file.target,
    path: safePath,
    contents: renderedContent,
    digest,
  };
}

function renderFiles(
  files: readonly TemplateFileTemplate[],
  context: Record<string, string>
): RenderedFile[] {
  return files.map((file) => renderTemplateFile(file, context));
}

function buildTemplateSummary(template: TemplatePack): TemplateSummary {
  return {
    name: template.name,
    description: template.description,
    fileCount: template.files.length,
  };
}

function createBranchSummary(node: PlanNode): BranchSummary {
  return {
    component: node.component,
    choice: node.choice,
    rationale: node.rationale,
    score: {
      total: node.score.total,
      complexity: node.score.complexity,
      risk: node.score.risk,
      perf: node.score.perf,
      devTime: node.score.devTime,
      depsReady: node.score.depsReady,
    },
  };
}

function filterFilesByScope(
  files: readonly TemplateFileTemplate[],
  scope: "branch" | "global"
): TemplateFileTemplate[] {
  return files.filter((file) => file.scope === scope);
}

interface BranchCoordinates {
  readonly branchName: string;
  readonly branchSlug: string;
  readonly worktreePath: string;
  readonly shortId: string;
}

function createBranchCoordinates(
  node: PlanNode,
  options: {
    readonly prefix: string;
    readonly worktreeRoot: string;
  }
): BranchCoordinates {
  const short = shortId(node.nodeId);
  const choiceSlug = buildChoiceSlug(node);
  const combined = `${choiceSlug}-${short}`;
  const branchSlug = sanitizePathSegments(combined);
  const branchName = options.prefix ? `${options.prefix}/${branchSlug}` : branchSlug;
  const worktreePath = options.worktreeRoot ? `${options.worktreeRoot}/${branchSlug}` : branchSlug;
  return {
    branchName,
    branchSlug,
    worktreePath,
    shortId: short,
  };
}

function createPackageJsonUpdates(
  scripts: Readonly<Record<string, string>>
): PackageJsonUpdate[] {
  const entries = Object.entries(scripts);
  if (entries.length === 0) {
    return [];
  }
  return [
    {
      path: "package.json",
      scripts,
    },
  ];
}

export function createScaffoldPlan(
  source: PlanSource,
  options: CreateScaffoldPlanOptions
): ScaffoldPlan {
  if (!options.template) {
    throw new Error("template is required to create a scaffold plan");
  }

  const limit = options.limit ?? DEFAULT_LIMIT;
  const baseBranch = options.baseBranch ?? DEFAULT_BASE_BRANCH;
  const branchPrefixInput = options.branchPrefix ?? `plan/${source.meta.specId}`;
  const worktreeRootInput = options.worktreeRoot ?? `worktrees/${source.meta.specId}`;
  const reusableWorkflowPathInput = options.reusableWorkflowPath ?? DEFAULT_REUSABLE_WORKFLOW_PATH;

  const normalizedPrefix = sanitizePathSegments(branchPrefixInput);
  const normalizedWorktreeRoot = sanitizePathSegments(worktreeRootInput);
  const reusableWorkflowPath = ensureNoParentTraversal(
    reusableWorkflowPathInput,
    "reusable workflow path"
  );

  const planNodes = source.nodes.filter((node) => node.component === "plan");
  if (planNodes.length === 0) {
    throw new Error("no plan nodes available for scaffolding");
  }

  const sorted = stableSort(planNodes, comparePlanNodes);
  const selected = sorted.slice(0, Math.max(1, limit));

  const branchTemplates = filterFilesByScope(options.template.files, "branch");
  const globalTemplates = filterFilesByScope(options.template.files, "global");

  const branches: ScaffoldBranchPlan[] = [];
  const index: ScaffoldPlanIndexEntry[] = [];

  for (const node of selected) {
    const coordinates = createBranchCoordinates(node, {
      prefix: normalizedPrefix,
      worktreeRoot: normalizedWorktreeRoot,
    });

    const context = {
      specId: source.meta.specId,
      templateName: options.template.name,
      baseBranch,
      branchName: coordinates.branchName,
      branchSlug: coordinates.branchSlug,
      nodeId: node.nodeId,
      shortId: coordinates.shortId,
    } satisfies Record<string, string>;

    const branchFiles = renderFiles(branchTemplates, context);
    const repoActions: RepoAction[] = [
      {
        type: "create-branch",
        branchName: coordinates.branchName,
        baseBranch,
      },
    ];

    branches.push({
      nodeId: node.nodeId,
      branchName: coordinates.branchName,
      branchSlug: coordinates.branchSlug,
      worktreePath: coordinates.worktreePath,
      summary: createBranchSummary(node),
      repoActions,
      files: branchFiles,
      packageJsonUpdates: [],
    });

    index.push({
      nodeId: node.nodeId,
      branchName: coordinates.branchName,
      worktreePath: coordinates.worktreePath,
    });
  }

  const globalContext = {
    specId: source.meta.specId,
    templateName: options.template.name,
    baseBranch,
    branchName: source.meta.specId,
    branchSlug: source.meta.specId,
    nodeId: source.meta.specId,
    shortId: source.meta.specId,
  } satisfies Record<string, string>;
  const globalFiles = renderFiles(globalTemplates, globalContext);

  const templateHash = hashObject({
    name: options.template.name,
    description: options.template.description,
    files: options.template.files.map((file) => ({
      sourcePath: file.sourcePath,
      scope: file.scope,
      target: file.target,
      relativePathTemplate: file.relativePathTemplate,
      contentHash: hashString(file.contentTemplate),
    })),
    scripts: options.template.packageJsonScripts,
  });

  return {
    meta: {
      version: SCAFFOLD_PLAN_VERSION,
      specId: source.meta.specId,
      specHash: source.meta.specHash,
      seed: source.meta.seed,
      planVersion: source.meta.version,
      templateName: options.template.name,
      templateHash,
      baseBranch,
      branchPrefix: normalizedPrefix,
      worktreeRoot: normalizedWorktreeRoot,
      reusableWorkflowPath,
      limit,
      totalCandidates: planNodes.length,
      selectedBranches: branches.length,
    },
    template: buildTemplateSummary(options.template),
    global: {
      files: globalFiles,
      packageJsonUpdates: createPackageJsonUpdates(options.template.packageJsonScripts),
    },
    branches,
    index,
  };
}
