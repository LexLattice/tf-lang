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

  it("passes when runtime matches JSON input", async () => {
    await fc.assert(
      fc.asyncProperty(fc.json({ maxDepth: 3 }), async (payload) => {
        const parsed = JSON.parse(payload);
        const runtime = JSON.parse(JSON.stringify(parsed));
        const result = await checkTransport(
          { cases: [{ name: "case", seed: "0x01", json: payload, value: runtime }] },
          ctx,
        );
        expect(result.ok).toBe(true);
        if (result.ok) {
          expect(result.value.casesChecked).toBe(1);
        }
      }),
      { seed: PASS_SEED, numRuns: 32 },
    );
  });

  it("fails when runtime diverges from decoded JSON", async () => {
    const json = JSON.stringify({ nested: { value: [1, 2, 3] } });
    const result = await checkTransport(
      {
        cases: [
          {
            name: "drift",
            seed: "0x02",
            json,
            value: { nested: { value: [1, 4, 3] } },
          },
        ],
      },
      ctx,
    );
    expect(result.ok).toBe(false);
    if (!result.ok) {
      expect(result.error.code).toBe("E_TRANSPORT_DRIFT");
      const details = result.error.details as { drifts?: ReadonlyArray<{ pointer: string }> } | undefined;
      const drift = details?.drifts?.[0];
      expect(drift?.pointer).toBe("/nested/value/1");
    }
  });

  it("fails when JSON cannot be parsed", async () => {
    const oracle = createTransportOracle();
    const result = await oracle.check(
      {
        cases: [
          {
            name: "invalid",
            seed: "0x03",
            json: "{\"broken\": true,,}",
            value: {},
          },
        ],
      },
      ctx,
    );
    expect(result.ok).toBe(false);
    if (!result.ok) {
      expect(result.error.code).toBe("E_TRANSPORT_DECODE");
      const details = result.error.details as { drifts?: ReadonlyArray<{ pointer: string; expected: unknown; actual: unknown }> } | undefined;
      const drift = details?.drifts?.[0];
      expect(drift?.pointer).toBe("");
      expect(drift?.expected).toBe("[valid json]");
      expect(typeof drift?.actual === "string").toBe(true);
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
