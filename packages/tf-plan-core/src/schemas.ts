import type { JSONSchemaType } from "ajv";
import type { PlanEdge, PlanGraph, PlanNode, ScoreBreakdown } from "./types.js";

export const scoreSchema: JSONSchemaType<ScoreBreakdown> = {
  $id: "https://tf-lang.dev/schema/tf-plan-score.json",
  type: "object",
  additionalProperties: false,
  required: ["total", "complexity", "risk", "perf", "devTime", "depsReady", "explain"],
  properties: {
    total: { type: "number" },
    complexity: { type: "number" },
    risk: { type: "number" },
    perf: { type: "number" },
    devTime: { type: "number" },
    depsReady: { type: "number" },
    explain: {
      type: "array",
      items: { type: "string" },
    },
  },
};

export const planNodeSchema: JSONSchemaType<PlanNode> = {
  $id: "https://tf-lang.dev/schema/tf-plan-node.json",
  type: "object",
  additionalProperties: false,
  required: ["nodeId", "specId", "component", "choice", "deps", "rationale", "score"],
  properties: {
    nodeId: { type: "string" },
    specId: { type: "string" },
    component: { type: "string" },
    choice: { type: "string" },
    deps: {
      type: "array",
      items: { type: "string" },
    },
    rationale: { type: "string" },
    score: scoreSchema,
  },
};

export const planEdgeSchema: JSONSchemaType<PlanEdge> = {
  $id: "https://tf-lang.dev/schema/tf-plan-edge.json",
  type: "object",
  additionalProperties: false,
  required: ["from", "to", "kind"],
  properties: {
    from: { type: "string" },
    to: { type: "string" },
    kind: { type: "string", enum: ["depends_on", "composes"] },
  },
};

export const planGraphSchema: JSONSchemaType<PlanGraph> = {
  $id: "https://tf-lang.dev/schema/tf-plan.json",
  type: "object",
  additionalProperties: false,
  required: ["nodes", "edges", "meta"],
  properties: {
    nodes: {
      type: "array",
      items: planNodeSchema,
      minItems: 1,
    },
    edges: {
      type: "array",
      items: planEdgeSchema,
    },
    meta: {
      type: "object",
      additionalProperties: false,
      required: ["seed", "specHash", "specId", "version"],
      properties: {
        seed: { type: "integer" },
        specHash: { type: "string" },
        specId: { type: "string" },
        version: { type: "string" },
      },
    },
  },
};

export type PlanNodeSchema = typeof planNodeSchema;
export type PlanGraphSchema = typeof planGraphSchema;
