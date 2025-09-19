import { describe, expect, it } from "vitest";
import {
  PLAN_GRAPH_VERSION,
  aggregateScores,
  createPlanGraphValidator,
  createSeededRng,
  deepFreeze,
  hashObject,
  hashString,
  shortId,
  stableId,
  stableSort,
} from "../src/index.js";

const BASE_ID_INPUT = {
  scope: "node",
  specId: "demo",
  component: "runtime",
  choice: "nodejs",
  seed: 42,
  version: PLAN_GRAPH_VERSION,
} as const;

describe("helpers", () => {
  it("computes stable id", () => {
    const id1 = stableId(BASE_ID_INPUT);
    const id2 = stableId(BASE_ID_INPUT);
    expect(id1).toBe(id2);
    expect(shortId(id1)).toHaveLength(12);
  });

  it("hashes objects canonically", () => {
    const hashA = hashObject({ b: 1, a: 2 });
    const hashB = hashObject({ a: 2, b: 1 });
    expect(hashA).toBe(hashB);
  });

  it("freezes deeply", () => {
    const target = deepFreeze({ foo: { bar: [1, 2, 3] } });
    expect(Object.isFrozen(target.foo.bar)).toBe(true);
  });

  it("sorts stably", () => {
    const result = stableSort(
      [
        { label: "a", score: 10 },
        { label: "b", score: 10 },
        { label: "c", score: 5 },
      ],
      (a, b) => b.score - a.score
    );
    expect(result.map((item) => item.label)).toEqual(["a", "b", "c"]);
  });

  it("produces deterministic rng", () => {
    const rng1 = createSeededRng(123);
    const rng2 = createSeededRng(123);
    expect([rng1.next(), rng1.next()]).toEqual([rng2.next(), rng2.next()]);
    expect(() => rng1.integer(0)).toThrow();
  });

  it("aggregates scores", () => {
    const result = aggregateScores([
      {
        total: 5,
        complexity: 2,
        risk: 1,
        perf: 3,
        devTime: 2,
        depsReady: 1,
        explain: ["first"],
      },
      {
        total: 10,
        complexity: 3,
        risk: 2,
        perf: 4,
        devTime: 2,
        depsReady: 3,
        explain: ["second"],
      },
    ]);
    expect(result.explain).toEqual(["first", "second"]);
    expect(result.total).toBeTypeOf("number");
  });

  it("validates plan graphs", () => {
    const validator = createPlanGraphValidator();
    const result = validator({
      nodes: [
        {
          nodeId: "abc",
          specId: "demo",
          component: "runtime",
          choice: "nodejs",
          deps: [],
          rationale: "demo",
          score: {
            total: 1,
            complexity: 1,
            risk: 1,
            perf: 1,
            devTime: 1,
            depsReady: 1,
            explain: [],
          },
        },
      ],
      edges: [],
      meta: {
        seed: 42,
        specHash: hashString("demo"),
        specId: "demo",
        version: PLAN_GRAPH_VERSION,
      },
    });
    expect(result.valid).toBe(true);
  });
});
