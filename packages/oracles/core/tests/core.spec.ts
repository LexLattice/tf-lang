import { describe, expect, it } from "vitest";

import {
  CanonicalizeError,
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

  it("canonicalizes containers deterministically", () => {
    const ctx = createOracleCtx("0xseed", { now: 0 });
    const map = new Map<unknown, unknown>();
    map.set({ id: 2, payload: { x: 2, y: 1 } }, { ok: true });
    map.set({ id: 1, payload: { y: 1, x: 2 } }, { ok: true });

    const input = {
      list: [3, 1, 2],
      bytes: new Uint8Array([3, 2, 1]),
      bag: new Set([3, 1, 2]),
      mapping: map,
    };

    const canonical = ctx.canonicalize(input);
    expect(canonical).toEqual({
      bag: [1, 2, 3],
      bytes: [3, 2, 1],
      list: [3, 1, 2],
      mapping: [
        {
          label: "{\"id\":1,\"payload\":{\"x\":2,\"y\":1}}\n",
          value: { ok: true },
        },
        {
          label: "{\"id\":2,\"payload\":{\"x\":2,\"y\":1}}\n",
          value: { ok: true },
        },
      ],
    });

    expect(canonicalJson(input)).toBe(
      "{\"bag\":[1,2,3],\"bytes\":[3,2,1],\"list\":[3,1,2],\"mapping\":[{\"label\":\"{\\\"id\\\":1,\\\"payload\\\":{\\\"x\\\":2,\\\"y\\\":1}}\\n\",\"value\":{\"ok\":true}},{\"label\":\"{\\\"id\\\":2,\\\"payload\\\":{\\\"x\\\":2,\\\"y\\\":1}}\\n\",\"value\":{\"ok\":true}}]}\n",
    );
  });

  it("pretty prints canonical JSON for reports", () => {
    expect(prettyCanonicalJson({ b: 1, a: 2 })).toBe(
      '{\n  "a": 2,\n  "b": 1\n}\n',
    );
  });

  it("rejects non-JSON values", () => {
    expect(() => canonicalize(undefined)).toThrow(TypeError);
    expect(() => canonicalize({ bad: undefined })).toThrow(TypeError);
    expect(() => canonicalize(new Date("2020-01-01T00:00:00Z"))).toThrow(TypeError);
    expect(() => canonicalize(BigInt(1))).toThrow(TypeError);
  });

  it("throws on duplicate canonical map labels", () => {
    const duplicate = new Map<unknown, unknown>();
    duplicate.set({ x: 1, y: 2 }, 1);
    duplicate.set({ y: 2, x: 1 }, 2);

    expect(() => canonicalize(duplicate)).toThrow(CanonicalizeError);
  });

  it("reports first differing pointer via deepEqual", () => {
    const actual = { a: { b: 1, c: 2 } };
    const expected = { a: { b: 1, c: 3 } };
    const result = deepEqual(actual, expected);
    expect(result).toEqual({ ok: false, path: "/a/c" });
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
});
