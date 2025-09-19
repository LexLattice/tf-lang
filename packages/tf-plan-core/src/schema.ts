import type { JSONSchema7 } from "json-schema";

const idPattern = "^[0-9a-f]{12,64}$";

const scoreBreakdownSchema: JSONSchema7 = {
  type: "object",
  additionalProperties: false,
  required: ["metric", "value", "rationale"],
  properties: {
    metric: { type: "string", minLength: 1 },
    value: { type: "number" },
    weight: { type: "number" },
    rationale: { type: "string", minLength: 1 }
  }
};

const scoreSchema: JSONSchema7 = {
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
      items: scoreBreakdownSchema,
      minItems: 0
    }
  }
};

export const planNodeSchema: JSONSchema7 = {
  $id: "https://tf-lang.dev/schema/tf-branch.schema.json",
  type: "object",
  additionalProperties: false,
  required: ["nodeId", "specId", "component", "choice", "deps", "rationale", "score"],
  properties: {
    nodeId: { type: "string", pattern: idPattern },
    specId: { type: "string", minLength: 1 },
    component: { type: "string", minLength: 1 },
    choice: { type: "string", minLength: 1 },
    deps: {
      type: "array",
      items: { type: "string", pattern: idPattern },
      uniqueItems: true
    },
    rationale: { type: "string", minLength: 1 },
    score: scoreSchema
  }
};

const planEdgeSchema: JSONSchema7 = {
  type: "object",
  additionalProperties: false,
  required: ["from", "to", "kind"],
  properties: {
    from: { type: "string", pattern: idPattern },
    to: { type: "string", pattern: idPattern },
    kind: { enum: ["dependency", "conflict", "composes"] }
  }
};

const planMetaSchema: JSONSchema7 = {
  type: "object",
  additionalProperties: false,
  required: ["seed", "specHash", "version", "generatedAt"],
  properties: {
    seed: { type: "integer" },
    specHash: { type: "string", pattern: "^[0-9a-f]{64}$" },
    version: { type: "string", minLength: 1 },
    generatedAt: { type: "string", format: "date-time" }
  }
};

export const planGraphSchema: JSONSchema7 = {
  $id: "https://tf-lang.dev/schema/tf-plan.schema.json",
  type: "object",
  additionalProperties: false,
  required: ["nodes", "edges", "meta"],
  properties: {
    nodes: {
      type: "array",
      items: planNodeSchema,
      minItems: 1
    },
    edges: {
      type: "array",
      items: planEdgeSchema,
      minItems: 0
    },
    meta: planMetaSchema
  }
};

const compareScoreSchema: JSONSchema7 = {
  type: "object",
  additionalProperties: false,
  required: ["score", "weight", "label", "explain"],
  properties: {
    label: { type: "string", minLength: 1 },
    score: { type: "number" },
    weight: { type: "number" },
    explain: { type: "string", minLength: 1 }
  }
};

const artifactRefSchema: JSONSchema7 = {
  type: "object",
  additionalProperties: false,
  required: ["label", "path"],
  properties: {
    label: { type: "string", minLength: 1 },
    path: { type: "string", minLength: 1 },
    type: { enum: ["json", "html", "log", "other"] }
  }
};

export const planCompareSchema: JSONSchema7 = {
  $id: "https://tf-lang.dev/schema/tf-compare.schema.json",
  type: "object",
  additionalProperties: false,
  required: ["meta", "branches", "recommended"],
  properties: {
    meta: {
      type: "object",
      additionalProperties: false,
      required: ["seed", "generatedAt", "version"],
      properties: {
        seed: { type: "integer" },
        generatedAt: { type: "string", format: "date-time" },
        version: { type: "string", minLength: 1 },
        inputs: {
          type: "object",
          additionalProperties: false,
          properties: {
            plan: { type: "string", minLength: 1 },
            scaffold: { type: "string", minLength: 1 },
            oracles: {
              type: "array",
              items: { type: "string", minLength: 1 }
            }
          }
        }
      }
    },
    branches: {
      type: "array",
      minItems: 1,
      items: {
        type: "object",
        additionalProperties: false,
        required: ["nodeId", "rank", "score", "scores", "summary"],
        properties: {
          nodeId: { type: "string", pattern: idPattern },
          rank: { type: "integer", minimum: 1 },
          score: { type: "number" },
          scores: {
            type: "array",
            items: compareScoreSchema
          },
          summary: { type: "string", minLength: 1 },
          artifacts: {
            type: "array",
            items: artifactRefSchema
          }
        }
      }
    },
    recommended: { type: "string", pattern: idPattern }
  }
};
