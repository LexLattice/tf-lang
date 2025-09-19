import { describe, expect, it } from "vitest";

import {
  canonicalStringify,
  createOracleCtx,
  defaultCanonicalize,
  err,
  ok,
  pointerFromSegments,
  withTrace,
} from "../src/index.js";

describe("oracles core", () => {
  it("wraps success values with deduplicated warnings", () => {
    const result = ok(42, ["  keep  ", "keep", "drop"]);
    expect(result).toEqual({
      ok: true,
      value: 42,
      warnings: ["drop", "keep"],
    });
  });

  it("normalizes error codes and explains", () => {
    const failure = err(" e_bad_input ", "  Something went wrong \n", { field: "x" });
    expect(failure).toEqual({
      ok: false,
      error: {
        code: "E_BAD_INPUT",
        explain: "Something went wrong",
        details: { field: "x" },
      },
    });
  });

  it("attaches traces with deduped frames", () => {
    const failure = withTrace(err("E_FAIL", "bad"), ["a", "a", "b"]);
    expect(failure.trace).toEqual(["a", "b"]);
  });

  it("canonicalizes arbitrarily nested data", () => {
    const ctx = createOracleCtx("0x1", { now: 0 });
    const input = {
      b: 1,
      a: [3, 2, undefined, -0, Number.POSITIVE_INFINITY],
      nested: { y: "x", x: "y" },
      when: new Date("2020-01-01T00:00:00Z"),
    };

    const canonical = ctx.canonicalize(input);
    expect(canonical).toEqual({
      a: [3, 2, null, 0, "Infinity"],
      b: 1,
      nested: { x: "y", y: "x" },
      when: "2020-01-01T00:00:00.000Z",
    });

    expect(canonicalStringify(input)).toBe(
      "{\"a\":[3,2,null,0,\"Infinity\"],\"b\":1,\"nested\":{\"x\":\"y\",\"y\":\"x\"},\"when\":\"2020-01-01T00:00:00.000Z\"}"
    );
  });

  it("provides a deterministic default canonicalizer", () => {
    const canonical = defaultCanonicalize({ z: 1, a: 2 });
    expect(Object.keys(canonical)).toEqual(["a", "z"]);
  });

  it("normalizes Set instances deterministically", () => {
    const ctx = createOracleCtx("0x2", { now: 0 });
    const input = new Set([
      { id: 2, payload: { x: 1, y: 2 } },
      { id: 1, payload: { y: 2, x: 1 } },
    ]);

    const canonical = ctx.canonicalize(input);
    expect(canonical).toEqual([
      { id: 1, payload: { x: 1, y: 2 } },
      { id: 2, payload: { x: 1, y: 2 } },
    ]);
  });

  it("builds RFC-6901 root pointers", () => {
    expect(pointerFromSegments([])).toBe("");
  });

  it("builds RFC-6901 pointers with escaped segments", () => {
    expect(pointerFromSegments(["alpha", "beta"])).toBe("/alpha/beta");
    expect(pointerFromSegments(["~", "/", ""])).toBe("/~0/~1/");
  });
});
