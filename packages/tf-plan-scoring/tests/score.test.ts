import { describe, expect, it } from "vitest";
import { scorePlanNode } from "../src/index.js";

const baseContext = {
  component: "runtime",
  choice: "Managed Node Runtime",
  metadata: {
    tags: ["managed", "ga"],
  },
  repoSignals: {
    componentSignals: {
      runtime: {
        stability: 0.9,
        performance: 0.7,
        velocity: 0.6,
        readiness: 0.8,
        incidents: 0.1,
      },
    },
  },
} as const;

describe("scorePlanNode", () => {
  it("is deterministic", () => {
    const first = scorePlanNode(baseContext);
    const second = scorePlanNode(baseContext);
    expect(first).toEqual(second);
  });

  it("responds to riskier choice", () => {
    const safer = scorePlanNode(baseContext);
    const riskier = scorePlanNode({
      ...baseContext,
      choice: "Experimental Runtime",
      metadata: { tags: ["experimental"] },
    });
    expect(riskier.risk).toBeGreaterThan(safer.risk);
    expect(riskier.total).toBeLessThan(safer.total);
  });
});
