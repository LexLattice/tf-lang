import { describe, it, expect } from "vitest";
import { equals, subsetOf, inRange, matchesRegex, nonEmpty } from "../src/index.js";

describe("equals", () => {
  it("ok", () => {
    expect(equals({ a: 1, b: [1, 2] }, { a: 1, b: [1, 2] }).ok).toBe(true);
  });
  it("fail with path", () => {
    const r = equals({ a: 1, b: [1, 2] }, { a: 1, b: [1, 3] });
    expect(r.ok).toBe(false);
    expect(r.code).toBe("E_NOT_EQUAL");
    expect(r.path).toBe("/b/1");
  });
  it("fail on type mismatch", () => {
    const r = equals(1, "1");
    expect(r.ok).toBe(false);
    expect(r.code).toBe("E_NOT_EQUAL");
    expect(r.path).toBe("/");
  });
  it("fail on null vs undefined", () => {
    const r = equals(null, undefined);
    expect(r.ok).toBe(false);
    expect(r.path).toBe("/");
  });
  it("fail on array vs object", () => {
    const r = equals([], {});
    expect(r.ok).toBe(false);
    expect(r.path).toBe("/");
  });
});

describe("subsetOf", () => {
  it("ok", () => {
    expect(subsetOf({ a: 1 }, { a: 1, b: 2 }).ok).toBe(true);
  });
  it("unknown field", () => {
    const r = subsetOf({ a: 1, x: 1 }, { a: 1, b: 2 });
    expect(r.ok).toBe(false);
    expect(r.code).toBe("E_FIELD_UNKNOWN");
    expect(r.path).toBe("/x");
  });
  it("nested ok", () => {
    const r = subsetOf({ a: { x: 1 } }, { a: { x: 1, y: 2 } });
    expect(r.ok).toBe(true);
  });
  it("nested unknown field", () => {
    const r = subsetOf({ a: { z: 3 } }, { a: { x: 1 } });
    expect(r.ok).toBe(false);
    expect(r.path).toBe("/a/z");
  });
  it("array subset ok", () => {
    expect(subsetOf([1], [1, 2]).ok).toBe(true);
  });
});

describe("inRange", () => {
  it("ok", () => {
    expect(inRange(5, 1, 10).ok).toBe(true);
  });
  it("fail", () => {
    const r = inRange(0, 1, 10);
    expect(r.ok).toBe(false);
    expect(r.code).toBe("E_OUT_OF_RANGE");
    expect(r.path).toBe("/");
  });
  it("at min", () => {
    expect(inRange(1, 1, 10).ok).toBe(true);
  });
  it("at max", () => {
    expect(inRange(10, 1, 10).ok).toBe(true);
  });
});

describe("matchesRegex", () => {
  it("ok", () => {
    expect(matchesRegex("abc123", /^[a-z]+\d+$/).ok).toBe(true);
  });
  it("fail", () => {
    const r = matchesRegex("abc", /^\d+$/);
    expect(r.ok).toBe(false);
    expect(r.code).toBe("E_REGEX_MISMATCH");
    expect(r.path).toBe("/");
  });
  it("global regex deterministic", () => {
    const re = /a/g;
    expect(matchesRegex("a", re).ok).toBe(true);
    expect(matchesRegex("a", re).ok).toBe(true);
  });
});

describe("nonEmpty", () => {
  it("ok", () => {
    expect(nonEmpty([1]).ok).toBe(true);
  });
  it("fail", () => {
    const r = nonEmpty("");
    expect(r.ok).toBe(false);
    expect(r.code).toBe("E_EMPTY");
    expect(r.path).toBe("/");
  });
  it("fail empty array", () => {
    const r = nonEmpty([]);
    expect(r.ok).toBe(false);
  });
  it("array with null values", () => {
    expect(nonEmpty([null]).ok).toBe(true);
  });
});

