import type { OracleResult } from "../result.js";
import { MESSAGES } from "../messages.js";
import { sortMapEntries, sortSetValues, isPlainObject } from "./structures.js";

/**
 * Performs a deep structural subset comparison.
 *
 * - Objects: every field in `actual` must exist in `expected` and be a subset recursively.
 * - Arrays: treated positionally (structural match), not mathematical multisets.
 * - Map: subset if each key exists in `expected` (by canonical form) and the associated value is subset.
 * - Set: subset if each value in `actual` exists in `expected` (deep equality).
 */

function escapePointerSegment(segment: string | number): string {
  return String(segment).replace(/~/g, "~0").replace(/\//g, "~1");
}

function pointerFromSegments(segments: Array<string | number>): string {
  if (segments.length === 0) return "/";
  return `/${segments.map(escapePointerSegment).join("/")}`;
}

function notSubset(segments: Array<string | number>): OracleResult {
  const code = "E_NOT_SUBSET" as const;
  return { ok: false, code, message: MESSAGES[code](), path: pointerFromSegments(segments) };
}

function subsetOfInner(actual: unknown, expected: unknown, segments: Array<string | number>): OracleResult {
  if (Object.is(actual, expected)) {
    return { ok: true };
  }

  if (actual === null || expected === null) {
    return notSubset(segments);
  }

  if (typeof actual !== "object" || typeof expected !== "object") {
    return Object.is(actual, expected) ? { ok: true } : notSubset(segments);
  }

  if (actual instanceof Map || expected instanceof Map) {
    if (!(actual instanceof Map) || !(expected instanceof Map)) {
      return notSubset(segments);
    }
    const expectedEntries = new Map(sortMapEntries(expected).map(entry => [entry.label, entry]));
    for (const entry of sortMapEntries(actual)) {
      const match = expectedEntries.get(entry.label);
      if (!match) {
        return {
          ok: false,
          code: "E_FIELD_UNKNOWN",
          message: "unknown field present",
          path: pointerFromSegments([...segments, entry.label]),
        };
      }
      const result = subsetOfInner(entry.value, match.value, [...segments, entry.label]);
      if (!result.ok) return result;
      expectedEntries.delete(entry.label);
    }
    return { ok: true };
  }

  if (actual instanceof Set || expected instanceof Set) {
    if (!(actual instanceof Set) || !(expected instanceof Set)) {
      return notSubset(segments);
    }
    const remaining = new Map(sortSetValues(expected).map(entry => [entry.label, entry]));
    for (const entry of sortSetValues(actual)) {
      const match = remaining.get(entry.label);
      if (!match) {
        return notSubset(segments);
      }
      const result = subsetOfInner(entry.value, match.value, [...segments, entry.label]);
      if (!result.ok) return result;
      remaining.delete(entry.label);
    }
    return { ok: true };
  }

  if (Array.isArray(actual) || Array.isArray(expected)) {
    if (!Array.isArray(actual) || !Array.isArray(expected)) {
      // If actual is an array but expected is not, surface the first index as unknown
      // to avoid emitting a trailing slash for nested roots.
      if (Array.isArray(actual)) {
        return {
          ok: false,
          code: "E_FIELD_UNKNOWN",
          message: "unknown field present",
          path: pointerFromSegments([...segments, 0]),
        };
      }
      return notSubset(segments);
    }
    for (let i = 0; i < actual.length; i++) {
      if (i >= expected.length) {
        return {
          ok: false,
          code: "E_FIELD_UNKNOWN",
          message: "unknown field present",
          path: pointerFromSegments([...segments, i]),
        };
      }
      const result = subsetOfInner(actual[i], expected[i], [...segments, i]);
      if (!result.ok) return result;
    }
    return { ok: true };
  }

  if (!isPlainObject(actual) || !isPlainObject(expected)) {
    return notSubset(segments);
  }

  for (const key of Object.keys(actual).sort()) {
    if (!(key in expected)) {
      return {
        ok: false,
        code: "E_FIELD_UNKNOWN",
        message: "unknown field present",
        path: pointerFromSegments([...segments, key]),
      };
    }
    const result = subsetOfInner((actual as Record<string, unknown>)[key], (expected as Record<string, unknown>)[key], [...segments, key]);
    if (!result.ok) return result;
  }
  return { ok: true };
}

export function subsetOf(actual: unknown, expected: unknown): OracleResult {
  return subsetOfInner(actual, expected, []);
}
