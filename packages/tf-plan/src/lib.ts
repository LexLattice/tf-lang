import { mkdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { ensureValidPlanGraph, freezePlanGraph, stableSort, type PlanGraph, type PlanNode } from "@tf-lang/tf-plan-core";
import { enumeratePlanGraph, type EnumerateOptions, type TfPlanSpec } from "@tf-lang/tf-plan-enum";
import { canonicalJson } from "@tf-lang/utils";

export interface EnumeratePlanOptions {
  readonly specPath: string;
  readonly seed?: number;
  readonly beamWidth?: number;
  readonly maxNodes?: number;
  readonly include?: Record<string, readonly string[]>;
  readonly exclude?: Record<string, readonly string[]>;
  readonly requires?: readonly string[];
}

export interface SummaryRow {
  readonly nodeId: string;
  readonly choice: string;
  readonly total: number;
  readonly risk: number;
}

export interface PlanSummary {
  readonly specId: string;
  readonly version: string;
  readonly nodes: readonly SummaryRow[];
}

export async function loadSpecFile(specPath: string): Promise<TfPlanSpec> {
  const raw = await readFile(specPath, "utf-8");
  const spec = JSON.parse(raw) as TfPlanSpec;
  if (!spec.name || !Array.isArray(spec.designSpace)) {
    throw new Error("invalid tf-plan spec: expected name and designSpace");
  }
  return spec;
}

export async function enumeratePlan(options: EnumeratePlanOptions): Promise<PlanGraph> {
  const spec = await loadSpecFile(options.specPath);
  const graph = enumeratePlanGraph(spec, {
    seed: options.seed,
    beamWidth: options.beamWidth,
    maxNodes: options.maxNodes,
    constraints: {
      include: options.include,
      exclude: options.exclude,
      requires: options.requires,
    },
  } satisfies EnumerateOptions);
  return graph;
}

export function summarizePlan(graph: PlanGraph, limit: number = 5): PlanSummary {
  const planNodes = graph.nodes.filter((node) => node.component === "plan");
  const rows = stableSort(planNodes, (a, b) => {
    const totalDiff = b.score.total - a.score.total;
    if (Math.abs(totalDiff) > 1e-6) {
      return totalDiff > 0 ? 1 : -1;
    }
    const riskDiff = a.score.risk - b.score.risk;
    if (Math.abs(riskDiff) > 1e-6) {
      return riskDiff > 0 ? 1 : -1;
    }
    return a.nodeId.localeCompare(b.nodeId);
  })
    .slice(0, limit)
    .map((node) => ({
      nodeId: node.nodeId,
      choice: node.choice,
      total: node.score.total,
      risk: node.score.risk,
    }));
  return {
    specId: graph.meta.specId,
    version: graph.meta.version,
    nodes: rows,
  };
}

export async function writePlanGraph(graph: PlanGraph, outDir: string): Promise<string> {
  await mkdir(outDir, { recursive: true });
  const outputPath = path.join(outDir, "plan.json");
  await writeFile(outputPath, canonicalJson(graph), "utf-8");
  return outputPath;
}

export async function writePlanNdjson(graph: PlanGraph, filePath: string, filter?: (node: PlanNode) => boolean): Promise<void> {
  await mkdir(path.dirname(filePath), { recursive: true });
  const nodes = filter ? graph.nodes.filter(filter) : graph.nodes;
  const lines = nodes.map((node) => JSON.stringify(node));
  await writeFile(filePath, `${lines.join("\n")}\n`, "utf-8");
}

export async function writeScoredPlan(graph: PlanGraph, filePath: string): Promise<void> {
  await mkdir(path.dirname(filePath), { recursive: true });
  const sorted = stableSort([...graph.nodes], (a, b) => {
    const totalDiff = b.score.total - a.score.total;
    if (Math.abs(totalDiff) > 1e-6) {
      return totalDiff > 0 ? 1 : -1;
    }
    const riskDiff = a.score.risk - b.score.risk;
    if (Math.abs(riskDiff) > 1e-6) {
      return riskDiff > 0 ? 1 : -1;
    }
    return a.nodeId.localeCompare(b.nodeId);
  });
  const scoredGraph: PlanGraph = {
    ...graph,
    nodes: sorted,
  };
  await writeFile(filePath, canonicalJson(scoredGraph), "utf-8");
}

export async function readPlanGraph(planPath: string): Promise<PlanGraph> {
  const raw = await readFile(planPath, "utf-8");
  const graph = JSON.parse(raw) as PlanGraph;
  return freezePlanGraph(ensureValidPlanGraph(graph));
}

