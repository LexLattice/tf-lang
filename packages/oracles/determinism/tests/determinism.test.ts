import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import fc from "fast-check";
import { createCtx } from "@tf/oracles-core";
import { determinismOracle } from "../src/index.js";
import type { DeterminismInput } from "../src/types.js";

const FIXTURES = new URL("../fixtures/", import.meta.url);

const clone = <T>(value: T): T => JSON.parse(JSON.stringify(value)) as T;

function loadFixture(name: string): DeterminismInput {
  const path = new URL(name, FIXTURES);
  return JSON.parse(readFileSync(path, "utf-8")) as DeterminismInput;
}

describe("determinism oracle fixtures", () => {
  it("accepts matching runs", async () => {
    const input = loadFixture("happy.json");
    const result = await determinismOracle(
      input,
      createCtx("0x6f2a7c9bbabc1234", 0)
    );
    expect(result.ok).toBe(true);
    if (result.ok) {
      expect(result.value.runs).toHaveLength(2);
      expect(result.value.seed).toBe("0x6f2a7c9bbabc1234");
    }
  });

  it("rejects a mismatched final state", async () => {
    const input = loadFixture("final-mismatch.json");
    const result = await determinismOracle(
      input,
      createCtx("0x6f2a7c9bbabc1234", 0)
    );
    expect(result.ok).toBe(false);
    if (!result.ok) {
      expect(result.error.code).toBe("E_DETERMINISM_FINAL_STATE");
      expect(result.error.details).toBeDefined();
    }
  });

  it("flags checkpoint label mismatches", async () => {
    const input = loadFixture("label-mismatch.json");
    const result = await determinismOracle(
      input,
      createCtx("0x6f2a7c9bbabc1234", 0)
    );
    expect(result.ok).toBe(false);
    if (!result.ok) {
      expect(result.error.code).toBe("E_DETERMINISM_CHECKPOINT_LABEL");
    }
  });
});

const runtimeNames = ["ts", "rs", "wasm"];

const jsonValueArb = fc.jsonValue({ maxDepth: 3 });
const checkpointArb = fc.array(
  fc.record({
    label: fc.hexaString({ minLength: 1, maxLength: 6 }),
    state: jsonValueArb,
  }),
  { maxLength: 4 }
);

const identicalInputArb = fc.record({
  checkpoints: checkpointArb,
  finalState: jsonValueArb,
}).chain((base) =>
  fc.shuffledSubarray<string>(runtimeNames, {
    minLength: 2,
    maxLength: runtimeNames.length,
  }).map((names) => ({
    runs: names.map((runtime) => ({
      runtime,
      checkpoints: base.checkpoints.map((cp) => ({
        label: cp.label,
        state: clone(cp.state),
      })),
      finalState: clone(base.finalState),
    })),
  }))
);

const mutatedInputArb = fc.record({
  checkpoints: checkpointArb,
  finalState: jsonValueArb,
}).chain((base) =>
  fc.tuple(
    fc.shuffledSubarray<string>(runtimeNames, {
      minLength: 2,
      maxLength: runtimeNames.length,
    }),
    fc.boolean(),
    fc.nat({ max: Math.max(base.checkpoints.length - 1, 0) })
  ).map(([names, mutateCheckpoint, cpIndex]) => {
    const runs = names.map((runtime) => ({
      runtime,
      checkpoints: base.checkpoints.map((cp) => ({
        label: cp.label,
        state: clone(cp.state),
      })),
      finalState: clone(base.finalState),
    }));
    const mutatedIndex = runs.length - 1;
    if (mutateCheckpoint && runs[mutatedIndex].checkpoints.length > 0) {
      const target = Math.min(cpIndex, runs[mutatedIndex].checkpoints.length - 1);
      const original = runs[mutatedIndex].checkpoints[target];
      runs[mutatedIndex].checkpoints[target] = {
        label: original.label,
        state: { mutated: true, original: clone(original.state) },
      };
    } else {
      const original = runs[mutatedIndex].finalState;
      runs[mutatedIndex].finalState = { mutated: true, original };
    }
    return { runs };
  })
);

describe("determinism oracle property tests", () => {
  const successConfig = { seed: 0x6f2a7c9b, numRuns: 40 } as const;
  it("accepts randomly generated identical runs", async () => {
    await fc.assert(
      fc.asyncProperty(identicalInputArb, async (input) => {
        const ctx = createCtx("0x6f2a7c9bbabc1234", 0);
        const first = await determinismOracle(input, ctx);
        const second = await determinismOracle(clone(input), ctx);
        expect(first).toEqual(second);
        expect(first.ok).toBe(true);
      }),
      successConfig
    );
  });

  const failureConfig = { seed: 0x5eadbeef, numRuns: 40 } as const;
  it("rejects mutated checkpoints or finals", async () => {
    await fc.assert(
      fc.asyncProperty(mutatedInputArb, async (input) => {
        const ctx = createCtx("0x5eadbeefcafebabe", 0);
        const first = await determinismOracle(input, ctx);
        const second = await determinismOracle(clone(input), ctx);
        expect(first).toEqual(second);
        expect(first.ok).toBe(false);
      }),
      failureConfig
    );
  });
});
