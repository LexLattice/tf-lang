import { describe, expect, it } from "vitest";

import { createOracleCtx } from "@tf/oracles-core";

import happy from "../fixtures/happy.json" assert { type: "json" };
import mismatchFixture from "../fixtures/mismatch.json" assert { type: "json" };
import { checkIdempotence } from "../src/index.js";

describe("checkIdempotence", () => {
  it("returns success when all cases are idempotent", async () => {
    const ctx = createOracleCtx("0xseed-idem-01");
    const result = await checkIdempotence(happy, ctx);
    expect(result.ok).toBe(true);
    if (!result.ok) {
      throw new Error("expected success");
    }
    expect(result.value).toEqual({ total: 1, passed: 1, failed: 0 });
  });

  it("returns failure with decorated pointer on mismatch", async () => {
    const ctx = createOracleCtx("0xseed-idem-02");
    const result = await checkIdempotence(mismatchFixture, ctx);
    expect(result.ok).toBe(false);
    if (result.ok) {
      throw new Error("expected failure");
    }
    const details = result.error.details as { report?: unknown; violations?: unknown };
    expect(details?.report).toEqual({
      total: 1,
      passed: 0,
      failed: 1,
      firstFail: { pointer: "/cases/0/3", left: undefined, right: 4 },
    });
    expect(details?.violations).toEqual([
      {
        caseName: "arrays-differ",
        seed: "0xseed-idem-02",
        mismatch: { pointer: "/cases/0/3", left: undefined, right: 4 },
      },
    ]);
  });

  it("escapes pointer segments for special characters", async () => {
    const ctx = createOracleCtx("0xseed-idem-03");
    const input = {
      cases: [
        {
          name: "escape",
          once: { "a/b": { "~": 1 } },
          twice: { "a/b": { "~": 2 } },
        },
      ],
    };
    const result = await checkIdempotence(input, ctx);
    expect(result.ok).toBe(false);
    if (result.ok) {
      throw new Error("expected failure");
    }
    const report = (result.error.details as { report?: { firstFail?: { pointer: string } } }).report;
    expect(report?.firstFail?.pointer).toBe("/cases/0/a~1b/~0");
  });
});
