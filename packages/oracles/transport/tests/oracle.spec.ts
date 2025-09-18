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
const FIXTURE_DIR = join(thisDir, "..", "fixtures");

describe("transport oracle", () => {
  const ctx = createOracleCtx("0xfeed", { now: 0 });

  it("accepts arbitrary JSON values", async () => {
    await fc.assert(
      fc.asyncProperty(fc.jsonValue({ maxDepth: 3 }), async (value) => {
        const result = await checkTransport({ value }, ctx);
        expect(result.ok).toBe(true);
        if (result.ok) {
          const roundTrip = JSON.parse(result.value.encoded) as unknown;
          expect(ctx.canonicalize(roundTrip)).toEqual(ctx.canonicalize(value));
        }
      }),
      { seed: PASS_SEED, numRuns: 32 },
    );
  });

  it("fails when runtime value cannot be represented as JSON", async () => {
    const value = new Set([1, 2, 3]);
    const result = await checkTransport({ value }, ctx);
    expect(result.ok).toBe(false);
    if (!result.ok) {
      expect(result.error.code).toBe("E_TRANSPORT_DIVERGED");
      const details = result.error.details as { mismatches?: ReadonlyArray<{ pointer: string; expected: unknown; actual: unknown }> } | undefined;
      const mismatch = details?.mismatches?.[0];
      expect(mismatch?.pointer).toBe("");
      expect(mismatch?.expected).toEqual([1, 2, 3]);
      expect(mismatch?.actual).toEqual({});
    }
  });

  it("surfaces serialization failures explicitly", async () => {
    const result = await checkTransport({ value: undefined }, ctx);
    expect(result.ok).toBe(false);
    if (!result.ok) {
      expect(result.error.code).toBe("E_TRANSPORT_SERIALIZE");
      const details = result.error.details as { reason?: string } | undefined;
      expect(details?.reason).toBe("JSON.stringify returned undefined");
    }
  });

  it("wires through the oracle factory", async () => {
    const oracle = createTransportOracle();
    const path = join(FIXTURE_DIR, "happy.json");
    const fixture = JSON.parse(readFileSync(path, "utf-8")) as { value: unknown };
    const result = await oracle.check({ value: fixture.value }, ctx);
    expect(result.ok).toBe(true);
  });
});

it("reports serialization errors for unsupported primitives", async () => {
  const ctx = createOracleCtx("0xfeed", { now: 0 });
  const result = await checkTransport({ value: BigInt(1) }, ctx);
  expect(result.ok).toBe(false);
  if (!result.ok) {
    expect(result.error.code).toBe("E_TRANSPORT_SERIALIZE");
    const details = result.error.details as { reason?: string } | undefined;
    expect(details?.reason).toContain("BigInt");
  }
});

function parseSeed(value: string): number {
  const parsed = Number.parseInt(value, 16);
  if (!Number.isFinite(parsed)) {
    throw new Error(`Invalid seed: ${value}`);
  }
  return parsed;
}
