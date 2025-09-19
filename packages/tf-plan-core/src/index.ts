import Ajv from "ajv";
import type { ErrorObject } from "ajv";
import { aggregateScores, createSeededRng, deepFreeze, freezePlanGraph, hashObject, hashString, shortId, stableId, stableSort } from "./helpers.js";
import { planEdgeSchema, planGraphSchema, planNodeSchema, scoreSchema } from "./schemas.js";
import type { PlanEdge, PlanGraph, PlanGraphMeta, PlanNode, PlanEdgeKind, ScoreBreakdown, SeededRng, StableIdInput } from "./types.js";
export type { PlanEdge, PlanGraph, PlanGraphMeta, PlanNode, PlanEdgeKind, ScoreBreakdown, SeededRng, StableIdInput } from "./types.js";
export { PLAN_GRAPH_VERSION } from "./types.js";
export { aggregateScores, createSeededRng, deepFreeze, freezePlanGraph, hashObject, hashString, shortId, stableId, stableSort } from "./helpers.js";
export { planEdgeSchema, planGraphSchema, planNodeSchema, scoreSchema } from "./schemas.js";

export interface ValidationResult {
  readonly valid: boolean;
  readonly errors: readonly ErrorObject[] | null | undefined;
}

export function createPlanGraphValidator(): (graph: PlanGraph) => ValidationResult {
  const ajv = new Ajv({
    allErrors: true,
    strict: false,
  });
  ajv.addSchema(scoreSchema);
  ajv.addSchema(planNodeSchema);
  ajv.addSchema(planEdgeSchema);
  const validate = ajv.compile(planGraphSchema);
  return (graph: PlanGraph) => ({
    valid: Boolean(validate(graph)),
    errors: validate.errors,
  });
}

export function ensureValidPlanGraph(graph: PlanGraph): PlanGraph {
  const validate = createPlanGraphValidator();
  const result = validate(graph);
  if (!result.valid) {
    const message = (result.errors ?? [])
      .map((err) => `${err.instancePath || "/"} ${err.message ?? "invalid"}`)
      .join("; ");
    throw new Error(`plan graph validation failed: ${message}`);
  }
  return graph;
}

export type { PlanGraphSchema, PlanNodeSchema } from "./schemas.js";
