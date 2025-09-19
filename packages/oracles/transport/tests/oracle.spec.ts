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
      expect(drift?.error).toBeUndefined();
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
      expect(drift?.error?.code).toBe("E_TRANSPORT_DECODE");
      expect(typeof drift?.error?.message).toBe("string");
    }
  });

  it("marks empty encoded payloads as decode failures", async () => {
    const result = await checkTransport(
      {
        cases: [
          {
            name: "empty",
            seed: "0x04",
            value: { ok: true },
            encoded: "",
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
      expect(drift?.error?.code).toBe("E_TRANSPORT_DECODE");
    }
  });

  it("treats Map values as unserializable", async () => {
    const result = await checkTransport(
      {
        cases: [
          {
            name: "map",
            seed: "0x05",
            value: new Map([
              ["one", 1],
              ["two", 2],
            ]),
          },
        ],
      },
      ctx,
    );

    expect(result.ok).toBe(false);
    if (!result.ok) {
      const details = result.error.details as { drifts?: ReadonlyArray<TransportDrift> };
      const drift = details.drifts?.[0];
      expect(drift?.after).toBe("[unserializable]");
      expect(drift?.error?.code).toBe("E_TRANSPORT_SERIALIZE");
      expect(drift?.error?.message).toContain("Map values");
    }
  });

  it("rejects BigInt values during serialization", async () => {
    const result = await checkTransport(
      {
        cases: [
          {
            name: "bigint",
            seed: "0x06",
            value: { counter: BigInt(1) },
          },
        ],
      },
      ctx,
    );

    expect(result.ok).toBe(false);
    if (!result.ok) {
      const details = result.error.details as { drifts?: ReadonlyArray<TransportDrift> };
      const drift = details.drifts?.[0];
      expect(drift?.after).toBe("[unserializable]");
      expect(drift?.error?.code).toBe("E_TRANSPORT_SERIALIZE");
      expect(drift?.error?.message).toContain("BigInt");
    }
  });

  it("rejects cyclic references during serialization", async () => {
    const cyclic: Record<string, unknown> = {};
    cyclic.self = cyclic;

    const result = await checkTransport(
      {
        cases: [
          {
            name: "cycle",
            seed: "0x07",
            value: cyclic,
          },
        ],
      },
      ctx,
    );

    expect(result.ok).toBe(false);
    if (!result.ok) {
      const details = result.error.details as { drifts?: ReadonlyArray<TransportDrift> };
      const drift = details.drifts?.[0];
      expect(drift?.after).toBe("[unserializable]");
      expect(drift?.error?.code).toBe("E_TRANSPORT_SERIALIZE");
      expect(drift?.error?.message).toContain("Cyclic");
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
