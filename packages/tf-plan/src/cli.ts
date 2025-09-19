#!/usr/bin/env node
import path from "node:path";
import { exit } from "node:process";
import {
  enumeratePlan,
  readPlanGraph,
  summarizePlan,
  writePlanGraph,
  writePlanNdjson,
  writeScoredPlan,
} from "./index.js";

interface EnumerateFlags {
  spec?: string;
  out?: string;
  seed?: number;
  beam?: number;
  maxNodes?: number;
  include: Record<string, string[]>;
  exclude: Record<string, string[]>;
  requires: string[];
}

interface ScoreFlags {
  plan?: string;
  out?: string;
}

interface ExportFlags {
  plan?: string;
  ndjson?: string;
  plansOnly: boolean;
}

function printHelp(): void {
  process.stdout.write(
    "Usage: tf-plan <command> [options]\n" +
      "\n" +
      "Commands:\n" +
      "  enumerate --spec <path> [--out <dir>] [--seed <n>] [--beam <n>] [--max-nodes <n>]\\n" +
      "            [--include component=choice]... [--exclude component=choice]... [--require capability]...\n" +
      "  score --plan <path> [--out <path>]\n" +
      "  export --plan <path> [--ndjson <path>] [--plans-only]\n"
  );
}

function sanitizeIdentifier(value: string, label: string): string {
  if (!/^[A-Za-z0-9:_-]+$/.test(value)) {
    throw new Error(`${label} must contain only alphanumeric characters, :, _, or -`);
  }
  return value;
}

function parseEnumerateFlags(args: string[]): EnumerateFlags {
  const flags: EnumerateFlags = {
    include: {},
    exclude: {},
    requires: [],
  };
  for (let i = 0; i < args.length; i += 1) {
    const token = args[i];
    switch (token) {
      case "--spec":
        flags.spec = args[++i];
        break;
      case "--out":
        flags.out = args[++i];
        break;
      case "--seed":
        flags.seed = Number.parseInt(args[++i] ?? "", 10);
        if (!Number.isFinite(flags.seed)) {
          throw new Error("--seed expects a numeric value");
        }
        break;
      case "--beam":
        flags.beam = Number.parseInt(args[++i] ?? "", 10);
        if (!Number.isFinite(flags.beam)) {
          throw new Error("--beam expects a numeric value");
        }
        break;
      case "--max-nodes":
        flags.maxNodes = Number.parseInt(args[++i] ?? "", 10);
        if (!Number.isFinite(flags.maxNodes)) {
          throw new Error("--max-nodes expects a numeric value");
        }
        break;
      case "--include": {
        const value = args[++i];
        if (!value || !value.includes("=")) {
          throw new Error("--include expects component=choice");
        }
        const [componentRaw, choiceRaw] = value.split("=", 2);
        const component = sanitizeIdentifier(componentRaw, "component");
        const choice = sanitizeIdentifier(choiceRaw, "choice");
        flags.include[component] = [...(flags.include[component] ?? []), choice];
        break;
      }
      case "--exclude": {
        const value = args[++i];
        if (!value || !value.includes("=")) {
          throw new Error("--exclude expects component=choice");
        }
        const [componentRaw, choiceRaw] = value.split("=", 2);
        const component = sanitizeIdentifier(componentRaw, "component");
        const choice = sanitizeIdentifier(choiceRaw, "choice");
        flags.exclude[component] = [...(flags.exclude[component] ?? []), choice];
        break;
      }
      case "--require": {
        const capability = args[++i];
        if (!capability) {
          throw new Error("--require expects a capability identifier");
        }
        flags.requires.push(sanitizeIdentifier(capability, "capability"));
        break;
      }
      case "--help":
      case "-h":
        printHelp();
        exit(0);
        break;
        break;
      default:
        throw new Error(`unknown flag: ${token}`);
    }
  }
  return flags;
}

function parseScoreFlags(args: string[]): ScoreFlags {
  const flags: ScoreFlags = {};
  for (let i = 0; i < args.length; i += 1) {
    const token = args[i];
    switch (token) {
      case "--plan":
        flags.plan = args[++i];
        if (!flags.plan) {
          throw new Error("--plan expects a path");
        }
        break;
      case "--out":
        flags.out = args[++i];
        if (!flags.out) {
          throw new Error("--out expects a path");
        }
        break;
      case "--help":
      case "-h":
        process.stdout.write("Usage: tf-plan score --plan <path> [--out <path>]\n");
        exit(0);
        break;
      default:
        throw new Error(`unknown flag: ${token}`);
    }
  }
  return flags;
}

function parseExportFlags(args: string[]): ExportFlags {
  const flags: ExportFlags = { plansOnly: false };
  for (let i = 0; i < args.length; i += 1) {
    const token = args[i];
    switch (token) {
      case "--plan":
        flags.plan = args[++i];
        if (!flags.plan) {
          throw new Error("--plan expects a path");
        }
        break;
      case "--ndjson":
        flags.ndjson = args[++i];
        if (!flags.ndjson) {
          throw new Error("--ndjson expects a path");
        }
        break;
      case "--plans-only":
        flags.plansOnly = true;
        break;
      case "--help":
      case "-h":
        process.stdout.write("Usage: tf-plan export --plan <path> [--ndjson <path>] [--plans-only]\n");
        exit(0);
        break;
      default:
        throw new Error(`unknown flag: ${token}`);
    }
  }
  return flags;
}

async function runEnumerate(args: string[]): Promise<number> {
  const flags = parseEnumerateFlags(args);
  if (!flags.spec) {
    throw new Error("--spec <path> is required");
  }
  const specPath = path.resolve(flags.spec);
  const outDir = path.resolve(flags.out ?? "out/t4/plan");
  const graph = await enumeratePlan({
    specPath,
    seed: typeof flags.seed === "number" ? flags.seed : undefined,
    beamWidth: typeof flags.beam === "number" ? flags.beam : undefined,
    maxNodes: typeof flags.maxNodes === "number" ? flags.maxNodes : undefined,
    include: flags.include,
    exclude: flags.exclude,
    requires: flags.requires,
  });
  const planPath = await writePlanGraph(graph, outDir);
  const summary = summarizePlan(graph, 5);
  process.stdout.write(
    `Plan graph written to ${planPath}\n` +
      `Spec: ${summary.specId} (version ${summary.version})\n` +
      summary.nodes
        .map(
          (row, index) =>
            `${index + 1}. ${row.choice} — total=${row.total.toFixed(2)} risk=${row.risk.toFixed(2)} (${row.nodeId})`
        )
        .join("\n") +
      (summary.nodes.length > 0 ? "\n" : "")
  );
  return 0;
}

async function runScore(args: string[]): Promise<number> {
  const flags = parseScoreFlags(args);
  if (!flags.plan) {
    throw new Error("--plan <path> is required");
  }
  const planPath = path.resolve(flags.plan);
  const graph = await readPlanGraph(planPath);
  const outPath = path.resolve(flags.out ?? path.join(path.dirname(planPath), "plan.scored.json"));
  await writeScoredPlan(graph, outPath);
  const summary = summarizePlan(graph, 5);
  process.stdout.write(
    `Scored plan written to ${outPath}\n` +
      summary.nodes
        .map(
          (row, index) =>
            `${index + 1}. ${row.choice} — total=${row.total.toFixed(2)} risk=${row.risk.toFixed(2)} (${row.nodeId})`
        )
        .join("\n") +
      (summary.nodes.length > 0 ? "\n" : "")
  );
  return 0;
}

async function runExport(args: string[]): Promise<number> {
  const flags = parseExportFlags(args);
  if (!flags.plan) {
    throw new Error("--plan <path> is required");
  }
  const planPath = path.resolve(flags.plan);
  const ndjsonPath = path.resolve(flags.ndjson ?? path.join(path.dirname(planPath), "plan.ndjson"));
  const graph = await readPlanGraph(planPath);
  const filter = flags.plansOnly ? (node: { component: string }) => node.component === "plan" : undefined;
  await writePlanNdjson(graph, ndjsonPath, filter);
  process.stdout.write(`Exported plan nodes to ${ndjsonPath}\n`);
  return 0;
}

async function main(): Promise<number> {
  const [, , command, ...args] = process.argv;
  try {
    switch (command) {
      case "enumerate":
        return await runEnumerate(args);
      case "score":
        return await runScore(args);
      case "export":
        return await runExport(args);
      case "--help":
      case "-h":
      case undefined:
        printHelp();
        return 0;
      default:
        process.stderr.write(`Unknown command: ${command}\n`);
        printHelp();
        return 1;
    }
  } catch (error) {
    process.stderr.write(`${(error as Error).message}\n`);
    return 1;
  }
}

main().then((code) => {
  exit(code);
});
