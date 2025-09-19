import { readFile } from "node:fs/promises";
import path from "node:path";
import { readPlanGraph } from "@tf-lang/tf-plan";
import type { PlanNode } from "@tf-lang/tf-plan-core";
import type { PlanSource } from "@tf-lang/tf-plan-scaffold-core";

function parsePlanLine(line: string, index: number): PlanNode {
  try {
    return JSON.parse(line) as PlanNode;
  } catch (error) {
    throw new Error(`failed to parse plan line ${index + 1}: ${(error as Error).message}`);
  }
}

async function readPlanNdjson(filePath: string): Promise<PlanNode[]> {
  const raw = await readFile(filePath, "utf-8");
  const lines = raw
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0);
  return lines.map((line, index) => parsePlanLine(line, index));
}

export interface LoadPlanOptions {
  readonly metaPath?: string;
}

export async function loadPlanSource(
  planPath: string,
  options: LoadPlanOptions = {}
): Promise<PlanSource> {
  const ext = path.extname(planPath);
  if (ext === ".json") {
    const graph = await readPlanGraph(planPath);
    return { nodes: graph.nodes, meta: graph.meta };
  }
  if (ext === ".ndjson") {
    const nodes = await readPlanNdjson(planPath);
    const metaPath = options.metaPath ?? path.join(path.dirname(planPath), "plan.json");
    const graph = await readPlanGraph(metaPath);
    const mismatched = nodes.find((node) => node.specId !== graph.meta.specId);
    if (mismatched) {
      throw new Error(
        `plan node ${mismatched.nodeId} belongs to spec ${mismatched.specId}, expected ${graph.meta.specId}`
      );
    }
    if (nodes.length !== graph.nodes.length) {
      throw new Error(
        `plan.ndjson contains ${nodes.length} nodes but plan.json has ${graph.nodes.length}`
      );
    }
    return { nodes, meta: graph.meta };
  }
  throw new Error(`unsupported plan file extension for ${planPath}`);
}
