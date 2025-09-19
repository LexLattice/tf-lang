import { existsSync } from "node:fs";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { spawn } from "node:child_process";
import { findRepoRoot } from "@tf-lang/utils";
import type {
  PackageJsonUpdate,
  RenderedFile,
  ScaffoldBranchPlan,
  ScaffoldPlan,
} from "@tf-lang/tf-plan-scaffold-core";

function toSystemPath(relativePath: string): string {
  const segments = relativePath.split("/").filter((segment) => segment.length > 0);
  if (segments.length === 0) {
    return "";
  }
  return path.join(...segments);
}

function resolveTarget(base: string, relativePath: string): string {
  const normalized = toSystemPath(relativePath);
  if (!normalized) {
    return base;
  }
  return path.join(base, normalized);
}

async function writeFileIfChanged(targetPath: string, contents: string): Promise<void> {
  if (existsSync(targetPath)) {
    const current = await readFile(targetPath, "utf-8");
    if (current === contents) {
      return;
    }
  }
  await mkdir(path.dirname(targetPath), { recursive: true });
  await writeFile(targetPath, contents, "utf-8");
}

async function applyRenderedFile(
  repoRoot: string,
  file: RenderedFile,
  branchWorktreePath: string | undefined,
  dryRun: boolean
): Promise<void> {
  let basePath = repoRoot;
  if (file.target === "workdir") {
    if (!branchWorktreePath) {
      throw new Error(`workdir file ${file.path} requires a branch worktree path`);
    }
    basePath = resolveTarget(repoRoot, branchWorktreePath);
  }
  const destination = resolveTarget(basePath, file.path);
  if (dryRun) {
    return;
  }
  await writeFileIfChanged(destination, file.contents);
}

async function applyPackageJsonUpdate(
  repoRoot: string,
  update: PackageJsonUpdate,
  dryRun: boolean
): Promise<void> {
  const targetPath = resolveTarget(repoRoot, update.path);
  if (dryRun) {
    return;
  }
  const raw = await readFile(targetPath, "utf-8");
  const pkg = JSON.parse(raw) as Record<string, unknown>;
  const scripts = { ...(pkg.scripts as Record<string, string> | undefined) };
  for (const [name, command] of Object.entries(update.scripts)) {
    scripts[name] = command;
  }
  const sortedScripts = Object.fromEntries(Object.entries(scripts).sort(([a], [b]) => a.localeCompare(b)));
  const next = { ...pkg, scripts: sortedScripts };
  const serialized = `${JSON.stringify(next, null, 2)}\n`;
  await writeFile(targetPath, serialized, "utf-8");
}

interface RunCommandOptions {
  readonly cwd: string;
  readonly stdio: "inherit" | "ignore" | "pipe";
  readonly allowFailure?: boolean;
}

async function runGit(args: readonly string[], options: RunCommandOptions): Promise<number> {
  return new Promise((resolve, reject) => {
    const child = spawn("git", args, {
      cwd: options.cwd,
      stdio: options.stdio,
      shell: false,
    });
    child.on("error", (error) => {
      reject(error);
    });
    child.on("exit", (code) => {
      if (code === 0 || options.allowFailure) {
        resolve(code ?? 0);
      } else {
        reject(new Error(`git ${args.join(" ")} exited with code ${code}`));
      }
    });
  });
}

async function ensureGitBranch(
  repoRoot: string,
  branchName: string,
  baseBranch: string,
  stdio: "inherit" | "ignore" | "pipe"
): Promise<void> {
  const existsCode = await runGit(
    ["show-ref", "--verify", "--quiet", `refs/heads/${branchName}`],
    { cwd: repoRoot, stdio, allowFailure: true }
  );
  if (existsCode === 0) {
    return;
  }
  await runGit(["rev-parse", "--verify", baseBranch], { cwd: repoRoot, stdio });
  await runGit(["branch", branchName, baseBranch], { cwd: repoRoot, stdio });
}

async function applyBranch(
  repoRoot: string,
  branch: ScaffoldBranchPlan,
  baseBranch: string,
  stdio: "inherit" | "ignore" | "pipe",
  dryRun: boolean
): Promise<void> {
  if (!dryRun) {
    for (const action of branch.repoActions) {
      if (action.type === "create-branch") {
        await ensureGitBranch(repoRoot, action.branchName, baseBranch, stdio);
      }
    }
  }

  if (!dryRun) {
    await mkdir(resolveTarget(repoRoot, branch.worktreePath), { recursive: true });
  }

  for (const file of branch.files) {
    await applyRenderedFile(repoRoot, file, branch.worktreePath, dryRun);
  }
  for (const update of branch.packageJsonUpdates) {
    await applyPackageJsonUpdate(repoRoot, update, dryRun);
  }
}

export interface ApplyOptions {
  readonly repoRoot?: string;
  readonly stdio?: "inherit" | "ignore" | "pipe";
  readonly dryRun?: boolean;
}

export async function applyScaffoldPlan(
  plan: ScaffoldPlan,
  options: ApplyOptions = {}
): Promise<void> {
  const repoRoot = options.repoRoot ?? findRepoRoot();
  const stdio = options.stdio ?? "inherit";
  const dryRun = options.dryRun ?? false;

  for (const file of plan.global.files) {
    await applyRenderedFile(repoRoot, file, undefined, dryRun);
  }
  for (const update of plan.global.packageJsonUpdates) {
    await applyPackageJsonUpdate(repoRoot, update, dryRun);
  }

  for (const branch of plan.branches) {
    await applyBranch(repoRoot, branch, plan.meta.baseBranch, stdio, dryRun);
  }
}
