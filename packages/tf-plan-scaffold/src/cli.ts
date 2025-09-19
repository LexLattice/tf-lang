#!/usr/bin/env node
import { exit } from "node:process";
import path from "node:path";
import {
  applyScaffoldPlan,
  createDraftPullRequests,
  formatPlanSummary,
  generateScaffoldPlan,
  readScaffoldPlan,
  writeScaffoldPlan,
} from "./lib.js";

interface GenerateFlags {
  planPath?: string;
  template?: string;
  outPath?: string;
  top?: number;
  base?: string;
  prefix?: string;
  worktrees?: string;
  reusableWorkflow?: string;
  meta?: string;
}

interface ApplyFlags {
  planPath?: string;
  repoRoot?: string;
  dryRun: boolean;
}

interface PrFlags {
  planPath?: string;
  openDraft: boolean;
}

function printHelp(): void {
  process.stdout.write(
    "Usage: tf-plan-scaffold <command> [options]\n\n" +
      "Commands:\n" +
      "  scaffold --plan <path> --template <name> [--out <path>] [--top <n>] [--base <name>]\\n" +
      "           [--prefix <branch-prefix>] [--worktrees <path>] [--reusable-workflow <path>]\\n" +
      "           [--meta <plan.json>]\n" +
      "  scaffold --apply <plan> [--repo-root <path>] [--dry-run]\n" +
      "  pr --plan <plan> [--open-draft]\n"
  );
}

function parseNumber(value: string | undefined, label: string): number {
  const parsed = Number.parseInt(value ?? "", 10);
  if (!Number.isFinite(parsed)) {
    throw new Error(`${label} expects a numeric value`);
  }
  return parsed;
}

function parseGenerateFlags(args: string[]): { mode: "generate"; flags: GenerateFlags } | { mode: "apply"; flags: ApplyFlags } {
  if (args.includes("--apply")) {
    const flags: ApplyFlags = { dryRun: false };
    for (let i = 0; i < args.length; i += 1) {
      const token = args[i];
      switch (token) {
        case "--apply":
          flags.planPath = args[++i];
          break;
        case "--repo-root":
          flags.repoRoot = args[++i];
          break;
        case "--dry-run":
          flags.dryRun = true;
          break;
        case "--help":
        case "-h":
          printHelp();
          exit(0);
          break;
        default:
          throw new Error(`unknown flag: ${token}`);
      }
    }
    if (!flags.planPath) {
      throw new Error("--apply expects a scaffold plan path");
    }
    return { mode: "apply", flags };
  }
  const flags: GenerateFlags = {};
  for (let i = 0; i < args.length; i += 1) {
    const token = args[i];
    switch (token) {
      case "--plan":
        flags.planPath = args[++i];
        break;
      case "--template":
        flags.template = args[++i];
        break;
      case "--out":
        flags.outPath = args[++i];
        break;
      case "--top":
        flags.top = parseNumber(args[++i], "--top");
        break;
      case "--base":
        flags.base = args[++i];
        break;
      case "--prefix":
        flags.prefix = args[++i];
        break;
      case "--worktrees":
        flags.worktrees = args[++i];
        break;
      case "--reusable-workflow":
        flags.reusableWorkflow = args[++i];
        break;
      case "--meta":
        flags.meta = args[++i];
        break;
      case "--help":
      case "-h":
        printHelp();
        exit(0);
        break;
      default:
        throw new Error(`unknown flag: ${token}`);
    }
  }
  return { mode: "generate", flags };
}

function parsePrFlags(args: string[]): PrFlags {
  const flags: PrFlags = { openDraft: false };
  for (let i = 0; i < args.length; i += 1) {
    const token = args[i];
    switch (token) {
      case "--plan":
      case "--apply":
        flags.planPath = args[++i];
        break;
      case "--open-draft":
        flags.openDraft = true;
        break;
      case "--help":
      case "-h":
        printHelp();
        exit(0);
        break;
      default:
        throw new Error(`unknown flag: ${token}`);
    }
  }
  if (!flags.planPath) {
    throw new Error("--plan expects a scaffold plan path");
  }
  return flags;
}

async function handleGenerate(flags: GenerateFlags): Promise<void> {
  if (!flags.planPath) {
    throw new Error("--plan is required");
  }
  if (!flags.template) {
    throw new Error("--template is required");
  }
  const outPath = flags.outPath ?? path.join("out", "t4", "scaffold", "index.json");
  const plan = await generateScaffoldPlan({
    planPath: flags.planPath,
    templateName: flags.template,
    limit: flags.top,
    baseBranch: flags.base,
    branchPrefix: flags.prefix,
    worktreeRoot: flags.worktrees,
    reusableWorkflowPath: flags.reusableWorkflow,
    planOptions: { metaPath: flags.meta },
  });
  await writeScaffoldPlan(plan, outPath);
  process.stdout.write(`${formatPlanSummary(plan)}\nPlan written to ${outPath}\n`);
}

async function handleApply(flags: ApplyFlags): Promise<void> {
  if (!flags.planPath) {
    throw new Error("--apply expects a scaffold plan path");
  }
  const plan = await readScaffoldPlan(flags.planPath);
  await applyScaffoldPlan(plan, { repoRoot: flags.repoRoot, dryRun: flags.dryRun });
  if (flags.dryRun) {
    process.stdout.write(`Dry-run complete for ${flags.planPath}\n`);
  } else {
    process.stdout.write(`Applied scaffold plan ${flags.planPath}\n`);
  }
}

async function handlePr(flags: PrFlags): Promise<void> {
  if (!flags.planPath) {
    throw new Error("--plan expects a scaffold plan path");
  }
  const plan = await readScaffoldPlan(flags.planPath);
  await createDraftPullRequests(plan, { openDraft: flags.openDraft });
}

async function main(): Promise<void> {
  const [command, ...rest] = process.argv.slice(2);
  if (!command || command === "--help" || command === "-h") {
    printHelp();
    return;
  }
  switch (command) {
    case "scaffold": {
      const parsed = parseGenerateFlags(rest);
      if (parsed.mode === "generate") {
        await handleGenerate(parsed.flags);
      } else {
        await handleApply(parsed.flags);
      }
      break;
    }
    case "pr": {
      const flags = parsePrFlags(rest);
      await handlePr(flags);
      break;
    }
    default:
      throw new Error(`unknown command: ${command}`);
  }
}

main().catch((error) => {
  process.stderr.write(`Error: ${(error as Error).message}\n`);
  exit(1);
});
