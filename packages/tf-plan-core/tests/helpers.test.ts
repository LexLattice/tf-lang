import { describe, expect, it } from "vitest";

import {
  deepFreeze,
  seedRng,
  seededShuffle,
  stableId,
  stableSort
} from "../src/index.js";

describe("stableId", () => {
  it("produces deterministic identifiers", () => {
    const first = stableId({
      specId: "spec",
      component: "frontend",
      choice: "react",
      seed: 42
    });
    const second = stableId({
      specId: "spec",
      component: "frontend",
      choice: "react",
      seed: 42
    });
    expect(second).toBe(first);
  });

  it("varies when any field changes", () => {
    const base = stableId({ specId: "spec", component: "a", choice: "x", seed: 42 });
    const diff = stableId({ specId: "spec", component: "b", choice: "x", seed: 42 });
    expect(diff).not.toBe(base);
  });
});

describe("seedRng", () => {
  it("returns reproducible random numbers", () => {
    const rngA = seedRng(123);
    const rngB = seedRng(123);
    const sequenceA = Array.from({ length: 5 }, () => rngA());
    const sequenceB = Array.from({ length: 5 }, () => rngB());
    expect(sequenceB).toEqual(sequenceA);
  });
});

describe("seededShuffle", () => {
  it("shuffles arrays in a deterministic manner", () => {
    const values = ["a", "b", "c", "d"];
    const rng = seedRng(5);
    const shuffled = seededShuffle(values, rng);
    expect(shuffled).toEqual(["b", "a", "d", "c"]);
    // original remains untouched
    expect(values).toEqual(["a", "b", "c", "d"]);
  });
});

describe("deepFreeze", () => {
  it("freezes nested objects", () => {
    const nested = deepFreeze({ a: { b: 1 } });
    expect(Object.isFrozen(nested)).toBe(true);
    expect(Object.isFrozen(nested.a)).toBe(true);
  });
});

describe("stableSort", () => {
  it("keeps equal items in original order", () => {
    const input = [
      { key: 1, order: "first" },
      { key: 1, order: "second" },
      { key: 0, order: "third" }
    ];
    const sorted = stableSort(input, (left, right) => left.key - right.key);
    expect(sorted.map((item) => item.order)).toEqual(["third", "first", "second"]);
  });
});
