import { describe, expect, it } from "vitest";

import {
  CanonicalizeError,
  NonJsonValueError,
  canonicalJson,
  canonicalize,
  createOracleCtx,
  deepEqual,
  err,
  ok,
  pointerFromSegments,
  prettyCanonicalJson,
  segmentsFromPointer,
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

  it("canonicalizes nested structures including map and set", () => {
    const ctx = createOracleCtx("0xseed", { now: 0 });
    const map = new Map<unknown, unknown>();
    map.set({ id: 2, payload: { x: 2, y: 1 } }, { ok: true });
    map.set({ id: 1, payload: { y: 1, x: 2 } }, { ok: true });

    const input = {
      unordered: { b: 1, a: [3, 2, 7, -0, Number.POSITIVE_INFINITY] },
      bytes: new Uint8Array([1, 2, 3]),
      bag: new Set([3, 1, 2]),
      mapping: map,
    };

    const canonical = ctx.canonicalize(input);
    expect(canonical).toEqual({
      bag: [1, 2, 3],
      bytes: [1, 2, 3],
      mapping: [
        {
          label:
            "{\"id\":1,\"payload\":{\"x\":2,\"y\":1}}\n",
          value: { ok: true },
        },
        {
          label:
            "{\"id\":2,\"payload\":{\"x\":2,\"y\":1}}\n",
          value: { ok: true },
        },
      ],
      unordered: {
        a: [3, 2, 7, 0, "Infinity"],
        b: 1,
      },
    });

    expect(canonicalJson(input)).toBe(
      "{\"bag\":[1,2,3],\"bytes\":[1,2,3],\"mapping\":[{\"label\":\"{\\\"id\\\":1,\\\"payload\\\":{\\\"x\\\":2,\\\"y\\\":1}}\\n\",\"value\":{\"ok\":true}},{\"label\":\"{\\\"id\\\":2,\\\"payload\\\":{\\\"x\\\":2,\\\"y\\\":1}}\\n\",\"value\":{\"ok\":true}}],\"unordered\":{\"a\":[3,2,7,0,\"Infinity\"],\"b\":1}}\n",
    );
    expect(prettyCanonicalJson(input, 2)).toBe(
      `${JSON.stringify(canonical, null, 2)}\n`,
    );
  });

  it("throws on duplicate canonical map labels", () => {
    const duplicate = new Map<unknown, unknown>();
    duplicate.set({ x: 1, y: 2 }, 1);
    duplicate.set({ y: 2, x: 1 }, 2);

    expect(() => canonicalize(duplicate)).toThrow(CanonicalizeError);
  });

  it("preserves array ordering", () => {
    const input = ["first", "second", "third"];
    const canonical = canonicalize(input);
    expect(canonical).toEqual(input);
  });

  it("reports first differing pointer via deepEqual", () => {
    const actual = { a: { b: [1, 2, 3] } };
    const expected = { a: { b: [1, 2, 4] } };
    const result = deepEqual(actual, expected);
    expect(result).toEqual({ ok: false, path: "/a/b/2" });
  });

  it("confirms equality when canonical forms match", () => {
    const left = { a: { x: 1, y: 2 } };
    const right = { a: { y: 2, x: 1 } };
    expect(deepEqual(left, right)).toEqual({ ok: true });
  });

  it("round-trips pointer segments", () => {
    const segments = ["root", 1, "~special/segment"] as const;
    const pointer = pointerFromSegments(segments.slice());
    expect(pointer).toBe("/root/1/~0special~1segment");
    expect(segmentsFromPointer(pointer)).toEqual(["root", 1, "~special/segment"]);
    expect(segmentsFromPointer("/")).toEqual([]);
  });

  it("rejects non-JSON values", () => {
    expect(() => canonicalJson(undefined)).toThrow(NonJsonValueError);
    expect(() => canonicalJson(new Date())).toThrow(NonJsonValueError);
    expect(() => canonicalize({ bad: undefined })).toThrow(NonJsonValueError);
    expect(() => canonicalJson(Symbol("x"))).toThrow(NonJsonValueError);
  });
});
