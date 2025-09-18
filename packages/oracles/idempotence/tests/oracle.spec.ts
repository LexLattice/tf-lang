import { readFileSync, readdirSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

import { describe, expect, it } from "vitest";
import * as fc from "fast-check";

import { createOracleCtx } from "@tf/oracles-core";
import { checkIdempotence } from "../src/index.js";
import type { IdempotenceInput } from "../src/types.js";

interface SeedsFile {
  readonly ts: {
    readonly passProperty: string;
    readonly failProperty: string;
  };
}

interface FixtureExpectation {
  readonly ok: boolean;
  readonly casesChecked: number;
  readonly pointer?: string;
}

interface IdempotenceFixture {
  readonly description: string;
  readonly input: IdempotenceInput;
  readonly expect: FixtureExpectation;
}

interface LoadedFixture {
  readonly file: string;
  readonly data: IdempotenceFixture;
}

const thisDir = dirname(fileURLToPath(import.meta.url));
const seedsPath = join(thisDir, "seeds.json");
const fixturesDir = join(thisDir, "..", "fixtures");

const seedsFile = JSON.parse(readFileSync(seedsPath, "utf-8")) as SeedsFile;
const PASS_SEED = parseSeed(seedsFile.ts.passProperty);
const FAIL_SEED = parseSeed(seedsFile.ts.failProperty);
const FIXTURES = loadFixtures();

const jsonValue = () => fc.jsonValue({ maxDepth: 3 });

describe("idempotence oracle", () => {
  const ctx = createOracleCtx("0xfeed", { now: 0 });

  it("passes when once and twice are canonical equivalents", async () => {
    await fc.assert(
      fc.asyncProperty(jsonValue(), async (value) => {
        const input: IdempotenceInput = {
          cases: [
            {
              name: "canonical",
              once: clone(value),
              twice: clone(value),
            },
          ],
        };
        const result = await checkIdempotence(input, ctx);
        expect(result.ok).toBe(true);
        if (result.ok) {
          expect(result.value.casesChecked).toBe(1);
          expect(result.value.mismatches).toHaveLength(0);
        }
      }),
      { numRuns: 64, seed: PASS_SEED },
    );
  });

  it("fails when the second run diverges", async () => {
    await fc.assert(
      fc.asyncProperty(jsonValue(), async (value) => {
        const input: IdempotenceInput = {
          cases: [
            {
              name: "mutated",
              once: clone(value),
              twice: perturb(value),
            },
          ],
        };
        const result = await checkIdempotence(input, ctx);
        expect(result.ok).toBe(false);
        if (!result.ok) {
          expect(result.error.code).toBe("E_NON_IDEMPOTENT");
        }
      }),
      { numRuns: 32, seed: FAIL_SEED },
    );
  });

  it("reports the deepest pointer on nested mismatches", async () => {
    const input: IdempotenceInput = {
      cases: [
        {
          name: "nested",
          once: { nested: { value: 1, meta: { hint: true } } },
          twice: { nested: { value: 2, meta: { hint: true } } },
        },
      ],
    };
    const result = await checkIdempotence(input, ctx);
    expect(result.ok).toBe(false);
    if (!result.ok) {
      expect(result.error.code).toBe("E_NON_IDEMPOTENT");
      const details = result.error.details as { mismatches?: IdempotenceMismatch[] } | undefined;
      const pointer = details?.mismatches?.[0]?.pointer;
      expect(pointer).toBe("/nested/value");
    }
  });

  it("detects null versus missing properties", async () => {
    const input: IdempotenceInput = {
      cases: [
        {
          name: "null-vs-missing",
          once: { value: null, other: 1 },
          twice: { other: 1 },
        },
      ],
    };
    const result = await checkIdempotence(input, ctx);
    expect(result.ok).toBe(false);
    if (!result.ok) {
      expect(result.error.code).toBe("E_NON_IDEMPOTENT");
      const details = result.error.details as { mismatches?: IdempotenceMismatch[] } | undefined;
      const pointer = details?.mismatches?.[0]?.pointer;
      expect(pointer).toBe("/value");
    }
  });
});

describe("idempotence fixtures", () => {
  for (const fixture of FIXTURES) {
    it(`matches ${fixture.file}`, async () => {
      const ctx = createOracleCtx("0xfeed", { now: 0 });
      const { input, expect: expectation } = fixture.data;
      const result = await checkIdempotence(input, ctx);
      if (expectation.ok) {
        expect(result.ok).toBe(true);
        if (result.ok) {
          expect(result.value.casesChecked).toBe(expectation.casesChecked);
        }
        return;
      }

      expect(result.ok).toBe(false);
      if (!result.ok) {
        expect(result.error.code).toBe("E_NON_IDEMPOTENT");
        const details = result.error.details as { mismatches?: IdempotenceMismatch[] } | undefined;
        const mismatches = details?.mismatches ?? [];
        expect(mismatches).toHaveLength(1);
        if (mismatches.length > 0) {
          expect(mismatches[0].pointer).toBe(expectation.pointer);
        }
      }
    });
  }
});

interface IdempotenceMismatch {
  readonly pointer: string;
}

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
  return entries.sort().map((file) => {
    const payload = JSON.parse(readFileSync(join(fixturesDir, file), "utf-8")) as IdempotenceFixture;
    return { file, data: payload };
  });
}
