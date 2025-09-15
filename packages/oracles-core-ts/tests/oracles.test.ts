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
});

