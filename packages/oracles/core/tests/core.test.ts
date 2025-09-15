import { describe, expect, it } from "vitest";
import {
  canonicalBuffer,
  canonicalStringify,
  canonicalize,
  createOracleCtx,
  defineOracle,
  deriveCtx,
  error,
  failure,
  formatFailure,
  fromError,
  isOk,
  mapValue,
  mergeWarnings,
  ok,
} from "../dist/index.js";

const sample = {
  b: 2,
  a: 1,
  nested: { z: 3, y: [2, 1], m: undefined as number | undefined },
};

describe("canonicalize", () => {
  it("sorts object keys and drops undefined", () => {
    const result = canonicalize(sample);
    expect(result).toEqual({
      a: 1,
      b: 2,
      nested: { y: [2, 1], z: 3 },
    });
  });

  it("stabilizes sets and maps", () => {
    const value = {
      set: new Set(["b", "a"]),
      map: new Map([
        ["b", { foo: 2 }],
        ["a", { foo: 1 }],
      ]),
    };
    const canon = canonicalize(value);
    expect(canon).toEqual({
      map: [
        { key: "a", value: { foo: 1 } },
        { key: "b", value: { foo: 2 } },
      ],
      set: ["a", "b"],
    });
    expect(canonicalStringify(value)).toBe(canonicalStringify(value));
  });

  it("canonicalBuffer is stable", () => {
    const first = canonicalBuffer({ b: 2, a: 1 });
    const second = canonicalBuffer({ a: 1, b: 2 });
    expect([...first]).toEqual([...second]);
  });
});

describe("context", () => {
  it("creates deterministic ctx", () => {
    const ctx = createOracleCtx({ seed: "seed-1", now: 123 });
    const again = ctx.canonicalize({ b: 1, a: 2 });
    expect(again).toEqual({ a: 2, b: 1 });
  });

  it("derives new ctx", () => {
    const base = createOracleCtx({ seed: "seed-1", now: 100 });
    const derived = deriveCtx(base, { now: 200 });
    expect(derived.seed).toBe("seed-1");
    expect(derived.now).toBe(200);
    expect(derived.canonicalize({ b: 1, a: 2 })).toEqual({ a: 2, b: 1 });
  });
});

describe("results", () => {
  it("ok dedupes warnings", () => {
    const result = ok(42, ["a", "b", "a"]);
    expect(result).toEqual({ ok: true, value: 42, warnings: ["a", "b"] });
  });

  it("mergeWarnings keeps sorted order", () => {
    const result = mergeWarnings(ok("value", ["a"]), ["c", "b"]);
    expect(result).toEqual({ ok: true, value: "value", warnings: ["a", "b", "c"] });
  });

  it("failure canonicalizes details", () => {
    const result = failure("E_TEST", "failed", {
      details: { b: 2, a: 1 },
      trace: ["b", "a", "a"],
    });
    expect(result).toEqual({
      ok: false,
      error: {
        code: "E_TEST",
        explain: "failed",
        details: { a: 1, b: 2 },
      },
      trace: ["a", "b"],
    });
  });

  it("fromError clones and canonicalizes", () => {
    const err = error("E", "boom", { b: 2, a: 1 });
    const result = fromError(err, ["z", "y"]);
    expect(result).toEqual({
      ok: false,
      error: { code: "E", explain: "boom", details: { a: 1, b: 2 } },
      trace: ["y", "z"],
    });
  });

  it("formatFailure renders message", () => {
    const result = failure("E_TEST", "boom");
    expect(formatFailure(result)).toBe("E_TEST: boom");
  });

  it("mapValue transforms ok", () => {
    const mapped = mapValue(ok({ x: 1 }), (value) => value.x + 1);
    expect(mapped).toEqual({ ok: true, value: 2 });
  });

  it("isOk type guards", () => {
    const good = ok(1);
    if (isOk(good)) {
      expect(good.value).toBe(1);
    } else {
      throw new Error("should not happen");
    }
  });
});

describe("defineOracle", () => {
  it("wraps sync check", async () => {
    const oracle = defineOracle("echo", (input: number) => ok(input + 1));
    const ctx = createOracleCtx({ seed: "seed-123", now: 0 });
    await expect(oracle.check(1, ctx)).resolves.toEqual({ ok: true, value: 2 });
  });

  it("wraps async check", async () => {
    const oracle = defineOracle("async", async (input: string) => ok(`${input}!`));
    const ctx = createOracleCtx({ seed: "seed-2", now: 0 });
    const result = await oracle.check("hi", ctx);
    expect(result).toEqual({ ok: true, value: "hi!" });
  });
});

