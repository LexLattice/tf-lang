import { readFileSync, readdirSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

import { describe, expect, it } from "vitest";
import * as fc from "fast-check";

import { createOracleCtx } from "@tf/oracles-core";
import { checkDeterminism, createDeterminismOracle } from "../src/index.js";
import type { DeterminismInput } from "../src/types.js";

interface SeedsFile {
  readonly ts: {
    readonly passProperty: string;
    readonly failProperty: string;
  };
}

interface FixtureExpectation {
  readonly ok: boolean;
  readonly casesChecked: number;
  readonly runsChecked: number;
  readonly mismatches?: ReadonlyArray<{
    readonly case: string;
    readonly seed: string;
    readonly run: string;
    readonly checkpoints: ReadonlyArray<string>;
  }>;
}

interface DeterminismFixture {
  readonly description: string;
  readonly input: DeterminismInput;
  readonly expect: FixtureExpectation;
}

interface LoadedFixture {
  readonly file: string;
  readonly data: DeterminismFixture;
}

const thisDir = dirname(fileURLToPath(import.meta.url));
const seedsPath = join(thisDir, "seeds.json");
const fixturesDir = join(thisDir, "..", "fixtures");

const seedsFile = JSON.parse(readFileSync(seedsPath, "utf-8")) as SeedsFile;

const PASS_SEED = parseSeed(seedsFile.ts.passProperty);
const FAIL_SEED = parseSeed(seedsFile.ts.failProperty);

const FIXTURES: LoadedFixture[] = loadFixtures();

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

describe("determinism fixtures", () => {
  for (const fixture of FIXTURES) {
    it(`matches ${fixture.file}`, async () => {
      const ctx = createOracleCtx("0xfeed", { now: 0 });
      const { input, expect: expectation } = fixture.data;
      expect(countCases(input)).toBe(expectation.casesChecked);
      expect(countRuns(input)).toBe(expectation.runsChecked);

      const result = await checkDeterminism(input, ctx);
      if (expectation.ok) {
        expect(result.ok).toBe(true);
        if (result.ok) {
          expect(result.value.casesChecked).toBe(expectation.casesChecked);
          expect(result.value.runsChecked).toBe(expectation.runsChecked);
        }
        return;
      }

      expect(result.ok).toBe(false);
      if (!result.ok) {
        expect(result.error.code).toBe("E_NON_DETERMINISTIC");
        const expectedMismatches = expectation.mismatches ?? [];
        const details = result.error.details as {
          readonly mismatches?: ReadonlyArray<{
            readonly case: string;
            readonly seed: string;
            readonly run: string;
            readonly mismatches: ReadonlyArray<{ readonly checkpoint: string }>;
          }>;
        } | undefined;
        const actualMismatches = details?.mismatches ?? [];
        expect(actualMismatches).toHaveLength(expectedMismatches.length);
        for (const expected of expectedMismatches) {
          const match = actualMismatches.find(
            (entry) => entry.case === expected.case && entry.run === expected.run,
          );
          expect(match).toBeDefined();
          if (match) {
            const actualCheckpoints = match.mismatches.map((item) => item.checkpoint).sort();
            const expectedCheckpoints = [...expected.checkpoints].sort();
            expect(actualCheckpoints).toEqual(expectedCheckpoints);
            expect(match.seed).toBe(expected.seed);
          }
        }
      }
    });
  }
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

function parseSeed(value: string): number {
  const parsed = Number.parseInt(value, 16);
  if (!Number.isFinite(parsed)) {
    throw new Error(`Invalid seed: ${value}`);
  }
  return parsed;
}

function loadFixtures(): LoadedFixture[] {
  const entries = readdirSync(fixturesDir).filter((file) => file.endsWith(".json"));
  return entries
    .sort()
    .map((file) => {
      const payload = JSON.parse(readFileSync(join(fixturesDir, file), "utf-8")) as DeterminismFixture;
      return { file, data: payload };
    });
}

function countRuns(input: DeterminismInput): number {
  return (input.cases ?? []).reduce((total, determinismCase) => total + determinismCase.runs.length, 0);
}

function countCases(input: DeterminismInput): number {
  return input.cases?.length ?? 0;
}
