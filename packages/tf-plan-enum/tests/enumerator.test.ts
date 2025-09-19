import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";
import { enumeratePlanGraph } from "../src/index.js";
import type { TfPlanSpec } from "../src/index.js";

function loadSpec(name: string): TfPlanSpec {
  const url = new URL(`../../../tests/specs/${name}`, import.meta.url);
  const raw = readFileSync(fileURLToPath(url), "utf-8");
  return JSON.parse(raw) as TfPlanSpec;
}

describe("enumeratePlanGraph", () => {
  it("produces deterministic plans with multiple branches", () => {
    const spec = loadSpec("demo.json");
    const first = enumeratePlanGraph(spec, { seed: 42, beamWidth: 8 });
    const second = enumeratePlanGraph(spec, { seed: 42, beamWidth: 8 });
    expect(first).toEqual(second);
    const planNodes = first.nodes.filter((node) => node.component === "plan");
    expect(planNodes.length).toBeGreaterThanOrEqual(3);
    expect(planNodes[0].score.explain.length).toBeGreaterThan(0);
    for (let i = 1; i < planNodes.length; i += 1) {
      const prev = planNodes[i - 1];
      const current = planNodes[i];
      if (prev.score.total !== current.score.total) {
        expect(prev.score.total).toBeGreaterThanOrEqual(current.score.total);
      } else {
        expect(prev.score.risk).toBeLessThanOrEqual(current.score.risk);
      }
    }
  });

  it("supports include constraints", () => {
    const spec = loadSpec("minimal.json");
    const graph = enumeratePlanGraph(spec, {
      constraints: {
        include: {
          api: ["graphql"],
        },
      },
    });
    const planNodes = graph.nodes.filter((node) => node.component === "plan");
    expect(planNodes).toHaveLength(2);
    for (const node of planNodes) {
      expect(node.choice).toContain("api=graphql");
    }
  });

  it("honors beam width limits", () => {
    const spec = loadSpec("minimal.json");
    const graph = enumeratePlanGraph(spec, { beamWidth: 1 });
    const planNodes = graph.nodes.filter((node) => node.component === "plan");
    expect(planNodes).toHaveLength(1);
  });

  it("enforces capability requirements", () => {
    const spec = loadSpec("constrained.json");
    const graph = enumeratePlanGraph(spec, {});
    const planNodes = graph.nodes.filter((node) => node.component === "plan");
    expect(planNodes).not.toHaveLength(0);
    for (const node of planNodes) {
      expect(node.choice.includes("frontend=")).toBe(true);
      expect(node.choice.includes("api=")).toBe(true);
    }
  });
});
