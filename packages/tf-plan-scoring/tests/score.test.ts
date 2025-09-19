import { describe, expect, it } from "vitest";

import { scorePlanNode } from "../src/score-plan-node.js";

const context = {
  component: "frontend",
  choice: "react-fast-refresh",
  metadata: {
    keywords: ["fast", "refresh"],
    maturity: 0.8,
    effort: 0.3,
    performance: 0.7,
    timeToDeliver: 0.4,
    dependencies: ["design-system"],
    risk: 0.35
  },
  repoSignals: {
    dependencyHealth: {
      "design-system": 0.9
    },
    componentVelocity: {
      frontend: 0.6
    },
    incidentHistory: [
      { component: "backend", severity: 0.4 }
    ],
    adoptionTrend: {
      "react-fast-refresh": 0.5
    }
  }
} as const;

describe("scorePlanNode", () => {
  it("produces a score with explain breakdown", () => {
    const result = scorePlanNode(context);
    expect(result.score.total).toBeGreaterThan(0);
    expect(result.score.explain).toHaveLength(5);
    expect(result.score.explain[0].metric <= result.score.explain[4].metric).toBe(true);
    expect(result.metrics[0].rationale.length).toBeGreaterThan(0);
  });

  it("is deterministic for the same input", () => {
    const first = scorePlanNode(context);
    const second = scorePlanNode(context);
    expect(second.score).toEqual(first.score);
  });

  it("penalizes high-risk scenarios", () => {
    const risky = scorePlanNode({
      component: "frontend",
      choice: "experimental-rewrite",
      repoSignals: {
        incidentHistory: [{ component: "frontend", severity: 0.9 }]
      }
    });
    const safe = scorePlanNode({ component: "frontend", choice: "stable-release" });
    expect(risky.score.risk).toBeLessThan(safe.score.risk);
  });
});
