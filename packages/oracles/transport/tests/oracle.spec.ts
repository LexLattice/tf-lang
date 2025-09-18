import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

import { describe, expect, it } from "vitest";
import * as fc from "fast-check";

import { createOracleCtx } from "@tf/oracles-core";
import { checkTransport, createTransportOracle } from "../src/index.js";

interface SeedsFile {
  readonly ts: {
    readonly passProperty: string;
  };
}

const thisDir = dirname(fileURLToPath(import.meta.url));
const seedsPath = join(thisDir, "seeds.json");
const seedsFile = JSON.parse(readFileSync(seedsPath, "utf-8")) as SeedsFile;

const PASS_SEED = parseSeed(seedsFile.ts.passProperty);

describe("transport oracle", () => {
  const ctx = createOracleCtx("0xfeed", { now: 0 });

  it("passes for JSON-compatible values", async () => {
    await fc.assert(
      fc.asyncProperty(fc.jsonValue({ maxDepth: 3 }), async (value) => {
        const result = await checkTransport({ value }, ctx);
        expect(result.ok).toBe(true);
        if (result.ok) {
          expect(result.value.casesChecked).toBe(1);
          expect(result.value.roundTripsChecked).toBe(1);
        }
      }),
      { seed: PASS_SEED, numRuns: 32 },
    );
  });

  it("supports explicit case lists", async () => {
    const oracle = createTransportOracle();
    const result = await oracle.check(
      {
        cases: [
          { name: "first", seed: "0x01", value: { alpha: 1 } },
          { name: "second", seed: "0x02", value: { beta: [1, 2, 3] } },
        ],
      },
      ctx,
    );
    expect(result.ok).toBe(true);
    if (result.ok) {
      expect(result.value.casesChecked).toBe(2);
      expect(result.value.roundTripsChecked).toBe(2);
    }
  });

  it("reports mismatches for unserializable runtime values", async () => {
    const value = new Set([1, 2]);
    const result = await checkTransport({ value }, ctx);
    expect(result.ok).toBe(false);
    if (!result.ok) {
      const details = result.error.details as { mismatches?: ReadonlyArray<{ pointer: string; expected: unknown; actual: unknown }> } | undefined;
      const mismatch = details?.mismatches?.[0];
      expect(mismatch?.pointer).toBe("");
      expect(mismatch?.expected).toEqual([1, 2]);
      expect(mismatch?.actual).toEqual({});
    }
  });

  it("emits RFC6901 pointers for nested mismatches", async () => {
    const ctx = createOracleCtx("0xfeed", { now: 0 });
    const result = await checkTransport({ value: { nested: new Set([true]) } }, ctx);
    expect(result.ok).toBe(false);
    if (!result.ok) {
      const details = result.error.details as { mismatches?: ReadonlyArray<{ pointer: string; expected: unknown; actual: unknown }> } | undefined;
      const mismatch = details?.mismatches?.[0];
      expect(mismatch?.pointer).toBe("/nested");
      expect(mismatch?.expected).toEqual([true]);
      expect(mismatch?.actual).toEqual({});
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
