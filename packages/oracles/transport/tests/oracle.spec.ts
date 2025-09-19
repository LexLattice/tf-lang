import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

import { describe, expect, it } from "vitest";
import * as fc from "fast-check";

import { createOracleCtx } from "@tf/oracles-core";
import { checkTransport, createTransportOracle } from "../src/index.js";
import type { TransportDrift } from "../src/index.js";

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

  it("accepts JSON-compatible values", async () => {
    await fc.assert(
      fc.asyncProperty(fc.jsonValue({ maxDepth: 3 }), async (value) => {
        const result = await checkTransport(
          { cases: [{ name: "case", seed: "0x01", value }] },
          ctx,
        );
        expect(result.ok).toBe(true);
        if (result.ok) {
          expect(result.value.casesChecked).toBe(1);
          expect(result.value.roundTripsChecked).toBe(1);
        }
      }),
      { seed: PASS_SEED, numRuns: 32 },
    );
  });

  it("detects properties dropped during serialization", async () => {
    const oracle = createTransportOracle();
    const result = await oracle.check(
      {
        cases: [
          {
            name: "function", 
            seed: "0x02",
            value: {
              keep: true,
              dropper(): void {
                // noop
              },
            },
          },
        ],
      },
      ctx,
    );

    expect(result.ok).toBe(false);
    if (!result.ok) {
      expect(result.error.code).toBe("E_TRANSPORT_DRIFT");
      const details = result.error.details as { drifts?: ReadonlyArray<TransportDrift> };
      const drift = details.drifts?.[0];
      expect(drift?.pointer).toBe("/dropper");
      expect(drift?.before).toBe("[fn dropper]");
      expect(drift?.after).toBe("[missing]");
    }
  });

  it("flags invalid pre-encoded JSON", async () => {
    const result = await checkTransport(
      {
        cases: [
          {
            name: "invalid",
            seed: "0x03",
            value: { ok: true },
            encoded: "{ not json }",
          },
        ],
      },
      ctx,
    );

    expect(result.ok).toBe(false);
    if (!result.ok) {
      const details = result.error.details as { drifts?: ReadonlyArray<TransportDrift> };
      const drift = details.drifts?.[0];
      expect(drift?.pointer).toBe("");
      expect(drift?.after).toBe("[invalid-json]");
      expect(drift?.issue?.code).toBe("E_TRANSPORT_DECODE");
    }
  });
});

it("treats maps as unserializable", async () => {
  const ctx = createOracleCtx("0xfeed", { now: 0 });
  const result = await checkTransport(
    {
      cases: [
        { name: "map", seed: "0x06", value: new Map([["key", 1]]) },
      ],
    },
    ctx,
  );
  expect(result.ok).toBe(false);
  if (!result.ok) {
    const details = result.error.details as { drifts?: ReadonlyArray<TransportDrift> };
    const drift = details.drifts?.[0];
    expect(drift?.pointer).toBe("");
    expect(drift?.after).toBe("[unserializable]");
    expect(drift?.issue?.code).toBe("E_TRANSPORT_SERIALIZE");
  }
});

it("captures JSON stringify errors for BigInt", async () => {
  const ctx = createOracleCtx("0xfeed", { now: 0 });
  const result = await checkTransport(
    {
      cases: [
        { name: "bigint", seed: "0x07", value: { value: BigInt(1) } },
      ],
    },
    ctx,
  );
  expect(result.ok).toBe(false);
  if (!result.ok) {
    const details = result.error.details as { drifts?: ReadonlyArray<TransportDrift> };
    const drift = details.drifts?.[0];
    expect(drift?.pointer).toBe("");
    expect(drift?.after).toBe("[unserializable]");
    expect(drift?.issue?.code).toBe("E_TRANSPORT_SERIALIZE");
  }
});

it("fails decoding for empty strings", async () => {
  const ctx = createOracleCtx("0xfeed", { now: 0 });
  const result = await checkTransport(
    {
      cases: [
        { name: "empty", seed: "0x08", value: { ok: true }, encoded: "" },
      ],
    },
    ctx,
  );
  expect(result.ok).toBe(false);
  if (!result.ok) {
    const details = result.error.details as { drifts?: ReadonlyArray<TransportDrift> };
    const drift = details.drifts?.[0];
    expect(drift?.pointer).toBe("");
    expect(drift?.after).toBe("[invalid-json]");
    expect(drift?.issue?.code).toBe("E_TRANSPORT_DECODE");
  }
});

function parseSeed(value: string): number {
  const parsed = Number.parseInt(value, 16);
  if (!Number.isFinite(parsed)) {
    throw new Error(`Invalid seed: ${value}`);
  }
  return parsed;
}
