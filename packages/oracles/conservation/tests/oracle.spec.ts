// @tf-test kind=product area=oracles speed=fast deps=node
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

import { describe, expect, it } from "vitest";
import * as fc from "fast-check";

import { createOracleCtx } from "@tf/oracles-core";
import { checkConservation, createConservationOracle } from "../src/index.js";

interface SeedsFile {
  readonly ts: {
    readonly passProperty: string;
  };
}

const thisDir = dirname(fileURLToPath(import.meta.url));
const seedsPath = join(thisDir, "seeds.json");
const seedsFile = JSON.parse(readFileSync(seedsPath, "utf-8")) as SeedsFile;

const PASS_SEED = parseSeed(seedsFile.ts.passProperty);
const FIXTURE_DIR = join(thisDir, "..", "fixtures");

describe("conservation oracle", () => {
  const ctx = createOracleCtx("0xfeed", { now: 0 });

  it("passes when declared keys remain equal", async () => {
    const keys = ["records", "warnings", "alerts"] as const;
    await fc.assert(
      fc.asyncProperty(
        fc.record({
          records: fc.integer({ min: -100, max: 100 }),
          warnings: fc.integer({ min: -100, max: 100 }),
          alerts: fc.integer({ min: -100, max: 100 }),
        }),
        fc.subarray(keys, { minLength: 1, maxLength: keys.length }),
        async (counts, subset) => {
          const before = { ...counts };
          const after = structuredClone(counts);
          const result = await checkConservation({ keys: subset, before, after }, ctx);
          expect(result.ok).toBe(true);
          if (result.ok) {
            expect(result.value.keysChecked).toBe(new Set(subset).size);
          }
        },
      ),
      { seed: PASS_SEED, numRuns: 32 },
    );
  });

  it("fails when a key drifts", async () => {
    const path = join(FIXTURE_DIR, "violation.json");
    const fixture = JSON.parse(readFileSync(path, "utf-8")) as Parameters<typeof checkConservation>[0];
    const result = await checkConservation(fixture, ctx);
    expect(result.ok).toBe(false);
    if (!result.ok) {
      expect(result.error.code).toBe("E_NOT_CONSERVED");
      const details = result.error.details as { violations?: ReadonlyArray<{ key: string; before: unknown; after: unknown; delta: unknown }> } | undefined;
      const violation = details?.violations?.[0];
      expect(violation?.key).toBe("records");
      expect(violation?.before).toBe(5);
      expect(violation?.after).toBe(4);
      expect(violation?.delta).toBe(-1);
    }
  });

  it("treats missing keys as mismatches", async () => {
    const result = await checkConservation(
      {
        keys: ["records"],
        before: { records: 1 },
        after: {},
      },
      ctx,
    );
    expect(result.ok).toBe(false);
    if (!result.ok) {
      const details = result.error.details as { violations?: ReadonlyArray<{ key: string; before: unknown; after: unknown }> } | undefined;
      const violation = details?.violations?.[0];
      expect(violation?.key).toBe("records");
      expect(violation?.before).toBe(1);
      expect(violation?.after).toBe("[missing]");
    }
  });

  it("falls back to union of snapshot keys when none declared", async () => {
    const oracle = createConservationOracle();
    const result = await oracle.check(
      {
        before: { records: 3, warnings: 0 },
        after: { records: 3, warnings: 0 },
      },
      ctx,
    );
    expect(result.ok).toBe(true);
    if (result.ok) {
      expect(result.value.keysChecked).toBe(2);
    }
  });
});

function parseSeed(value: string): number {
  const parsed = Number.parseInt(value, 16);
  if (!Number.isFinite(parsed)) {
    throw new Error(`Invalid seed: ${value}`);
  }
  return parsed;
}
