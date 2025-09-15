import { describe, expect, it } from "vitest";
import * as fc from "fast-check";

import { createOracleCtx } from "@tf/oracles-core";
import { checkDeterminism, createDeterminismOracle } from "../src/index.js";

const PASS_SEED = 0x5a17ce;
const FAIL_SEED = 0x9b1d2c;

const jsonValue = () => fc.jsonValue({ maxDepth: 3 });

const runTemplateArb = fc.record({
  final: jsonValue(),
  checkpoints: fc.dictionary(fc.hexaString({ minLength: 1, maxLength: 6 }), jsonValue(), {
    maxKeys: 4,
  }),
});

const runIdsArb = fc.uniqueArray(fc.hexaString({ minLength: 3, maxLength: 8 }), {
  minLength: 2,
  maxLength: 5,
});

describe("determinism oracle", () => {
  const ctx = createOracleCtx("0xfeed", { now: 0 });

  it("passes when every run matches", async () => {
    await fc.assert(
      fc.asyncProperty(runTemplateArb, runIdsArb, async (template, runIds) => {
        const runs = runIds.map((runId) => ({
          runId,
          final: clone(template.final),
          checkpoints: clone(template.checkpoints),
        }));

        const result = await checkDeterminism(
          { cases: [{ name: "case", seed: "0x01", runs }] },
          ctx,
        );
        expect(result.ok).toBe(true);
        if (result.ok) {
          expect(result.value.casesChecked).toBe(1);
          expect(result.value.runsChecked).toBe(runs.length);
        }
      }),
      { seed: PASS_SEED, numRuns: 64 },
    );
  });

  it("flags drifted checkpoints", async () => {
    await fc.assert(
      fc.asyncProperty(
        runTemplateArb,
        runIdsArb,
        fc.boolean(),
        async (template, runIds, mutateCheckpoint) => {
          const baselineRuns = runIds.map((runId) => ({
            runId,
            final: clone(template.final),
            checkpoints: clone(template.checkpoints),
          }));
          const mutated = baselineRuns.map((run, index) => {
            if (index !== baselineRuns.length - 1) {
              return run;
            }
            const updated = {
              runId: run.runId,
              final: clone(run.final),
              checkpoints: clone(run.checkpoints),
            };
            if (mutateCheckpoint && Object.keys(updated.checkpoints).length > 0) {
              const [first] = Object.keys(updated.checkpoints);
              updated.checkpoints[first] = perturb(updated.checkpoints[first]);
            } else if (mutateCheckpoint) {
              updated.checkpoints.__mut__ = perturb(run.final);
            } else {
              updated.final = perturb(run.final);
            }
            return updated;
          });

          const result = await checkDeterminism(
            { cases: [{ name: "case", seed: "0x02", runs: mutated }] },
            ctx,
          );
          expect(result.ok).toBe(false);
          if (!result.ok) {
            expect(result.error.code).toBe("E_NON_DETERMINISTIC");
            expect(result.error.details).toBeDefined();
          }
        },
      ),
      { seed: FAIL_SEED, numRuns: 48 },
    );
  });

  it("ignores object key ordering", async () => {
    const oracle = createDeterminismOracle();
    const result = await oracle.check(
      {
        cases: [
          {
            name: "ordering",
            seed: "0x03",
            runs: [
              { runId: "A", final: { b: 1, a: 2 }, checkpoints: { snap: { z: 1, x: 2 } } },
              { runId: "B", final: { a: 2, b: 1 }, checkpoints: { snap: { x: 2, z: 1 } } },
            ],
          },
        ],
      },
      ctx,
    );
    expect(result.ok).toBe(true);
  });
});

function clone<T>(value: T): T {
  return structuredClone(value);
}

function perturb(value: unknown): unknown {
  if (typeof value === "number") {
    if (!Number.isFinite(value)) {
      return `${value}`;
    }
    if (!Number.isSafeInteger(value)) {
      return `${value}__mutated`;
    }
    return value + 1;
  }
  if (typeof value === "string") {
    return `${value}__mutated`;
  }
  if (Array.isArray(value)) {
    return [...value, "__mutated__"];
  }
  if (value && typeof value === "object") {
    return { ...(value as Record<string, unknown>), __mutated__: true };
  }
  if (typeof value === "boolean") {
    return !value;
  }
  return { __mutated__: value };
}
