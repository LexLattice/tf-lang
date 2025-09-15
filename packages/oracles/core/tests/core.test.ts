import { describe, expect, it } from "vitest";
import {
  canonicalJSONString,
  canonicalize,
  createCtx,
  err,
  ok,
} from "../src/index.js";

describe("canonicalize", () => {
  it("sorts object keys and formats floats", () => {
    const value = {
      z: 4,
      a: 1,
      list: [3, 1.2345678901234],
      nested: {
        c: 3,
        b: 2,
        a: 1,
      },
    };
    const canonical = canonicalize(value);
    expect(canonical).toEqual({
      a: 1,
      list: [3, "1.234567890123"],
      nested: { a: 1, b: 2, c: 3 },
      z: 4,
    });
  });

  it("canonicalizes sets deterministically", () => {
    const fromSet = canonicalize(new Set([3, 1, 2]));
    expect(fromSet).toEqual([1, 2, 3]);
  });

  it("drops undefined fields", () => {
    const value = { a: 1, b: undefined, c: null };
    expect(canonicalize(value)).toEqual({ a: 1, c: null });
  });
});

describe("helpers", () => {
  it("builds ok results with optional warnings", () => {
    expect(ok("value")).toEqual({ ok: true, value: "value" });
    const warned = ok("value", ["warn"]);
    expect(warned).toEqual({ ok: true, value: "value", warnings: ["warn"] });
  });

  it("builds error results and preserves trace", () => {
    const error = err("E_TEST", "failed", {
      details: { leak: 5 },
      trace: ["step1", "step2"],
    });
    expect(error).toEqual({
      ok: false,
      error: {
        code: "E_TEST",
        explain: "failed",
        details: { leak: 5 },
      },
      trace: ["step1", "step2"],
    });
  });
});

describe("context", () => {
  it("uses canonicalize helper", () => {
    const ctx = createCtx("0x1", 0);
    const canonical = ctx.canonicalize({ b: 2, a: 1.5 });
    expect(canonical).toEqual({ a: "1.500000000000", b: 2 });
    expect(canonicalJSONString({ b: 2, a: 1.5 })).toBe(
      '{"a":"1.500000000000","b":2}'
    );
  });
});
