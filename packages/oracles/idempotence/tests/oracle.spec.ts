import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

import { describe, expect, it } from "vitest";
import * as fc from "fast-check";

import { createOracleCtx } from "@tf/oracles-core";
import { checkIdempotence, createIdempotenceOracle } from "../src/index.js";

interface SeedsFile {
  readonly ts: {
    readonly passProperty: string;
  };
}

const thisDir = dirname(fileURLToPath(import.meta.url));
const seedsPath = join(thisDir, "seeds.json");
const seedsFile = JSON.parse(readFileSync(seedsPath, "utf-8")) as SeedsFile;

const PASS_SEED = parseSeed(seedsFile.ts.passProperty);

describe("idempotence oracle", () => {
  const ctx = createOracleCtx("0xfeed", { now: 0 });

  it("passes when repeated applications are equal", async () => {
    await fc.assert(
      fc.asyncProperty(fc.jsonValue({ maxDepth: 3 }), fc.integer({ min: 2, max: 5 }), async (baseline, count) => {
        const applications = Array.from({ length: count }, (_, index) => ({
          iteration: index,
          value: index === 0 ? baseline : structuredClone(baseline),
        }));
        const result = await checkIdempotence(
          { cases: [{ name: "case", seed: "0x01", applications }] },
          ctx,
        );
        expect(result.ok).toBe(true);
        if (result.ok) {
          expect(result.value.casesChecked).toBe(1);
          expect(result.value.applicationsChecked).toBe(count - 1);
        }
      }),
      { seed: PASS_SEED, numRuns: 32 },
    );
  });

  it("fails when later applications diverge", async () => {
    const result = await checkIdempotence(
      {
        cases: [
          {
            name: "drift",
            seed: "0x02",
            applications: [
              { iteration: 0, value: { nested: { value: [1, 2, 3] } } },
              { iteration: 1, value: { nested: { value: [1, 4, 3] } } },
            ],
          },
        ],
      },
      ctx,
    );
    expect(result.ok).toBe(false);
    if (!result.ok) {
      expect(result.error.code).toBe("E_NOT_IDEMPOTENT");
      const details = result.error.details as { mismatches?: ReadonlyArray<{ pointer: string }> } | undefined;
      const mismatches = details?.mismatches ?? [];
      expect(mismatches).toHaveLength(1);
      expect(mismatches[0]?.pointer).toBe("/nested/value/1");
    }
  });

  it("ignores key ordering differences", async () => {
    const oracle = createIdempotenceOracle();
    const result = await oracle.check(
      {
        cases: [
          {
            name: "ordering",
            seed: "0x03",
            applications: [
              { iteration: 0, value: { id: 1, payload: { b: 2, a: 3 } } },
              { iteration: 1, value: { payload: { a: 3, b: 2 }, id: 1 } },
            ],
          },
        ],
      },
      ctx,
    );
    expect(result.ok).toBe(true);
  });
});

it("surfaces missing fields with JSON pointers", async () => {
  const ctx = createOracleCtx("0xfeed", { now: 0 });
  const result = await checkIdempotence(
    {
      cases: [
        {
          name: "missing",
          seed: "0x04",
          applications: [
            { iteration: 0, value: { keep: true } },
            { iteration: 1, value: { keep: true, extra: 42 } },
          ],
        },
      ],
    },
    ctx,
  );
  expect(result.ok).toBe(false);
  if (!result.ok) {
    const details = result.error.details as { mismatches?: ReadonlyArray<{ pointer: string; expected: unknown; actual: unknown }> } | undefined;
    const entry = details?.mismatches?.[0];
    expect(entry?.pointer).toBe("/extra");
    expect(entry?.expected).toBe("[missing]");
    expect(entry?.actual).toBe(42);
  }
});

function parseSeed(value: string): number {
  const parsed = Number.parseInt(value, 16);
  if (!Number.isFinite(parsed)) {
    throw new Error(`Invalid seed: ${value}`);
  }
  return parsed;
}
