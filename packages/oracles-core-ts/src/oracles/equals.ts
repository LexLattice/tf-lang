import type { OracleResult } from "../result.js";
import { MESSAGES } from "../messages.js";
import { sortMapEntries, sortSetValues, isPlainObject } from "./structures.js";

function diffPath(a: any, b: any, base: string = ""): string | null {
  const path = (k: string | number) =>
    base + "/" + String(k).replace(/~/g, "~0").replace(/\//g, "~1");
  if (Object.is(a, b)) return null;

  if (a instanceof Map || b instanceof Map) {
    if (!(a instanceof Map) || !(b instanceof Map)) {
      return base || "/";
    }
    const entriesA = sortMapEntries(a);
    const entriesB = sortMapEntries(b);
    if (entriesA.length !== entriesB.length) {
      return base || "/";
    }
    for (let i = 0; i < entriesA.length; i++) {
      const left = entriesA[i];
      const right = entriesB[i];
      if (left.label !== right.label) {
        return path(left.label);
      }
      const childPath = diffPath(left.value, right.value, path(left.label));
      if (childPath) return childPath;
    }
    return null;
  }

  if (a instanceof Set || b instanceof Set) {
    if (!(a instanceof Set) || !(b instanceof Set)) {
      return base || "/";
    }
    const valuesA = sortSetValues(a);
    const valuesB = sortSetValues(b);
    if (valuesA.length !== valuesB.length) {
      return base || "/";
    }
    for (let i = 0; i < valuesA.length; i++) {
      const childPath = diffPath(valuesA[i].value, valuesB[i].value, path(i));
      if (childPath) return childPath;
    }
    return null;
  }

  if (
    a === null ||
    b === null ||
    typeof a !== "object" ||
    typeof b !== "object"
  ) {
    return base || "/";
  }

  if (Array.isArray(a) !== Array.isArray(b)) {
    return base || "/";
  }

  if (Array.isArray(a)) {
    // Both are arrays
    const len = Math.max(a.length, b.length);
    for (let i = 0; i < len; i++) {
      if (i >= a.length || i >= b.length) return path(i);
      const p = diffPath(a[i], b[i], path(i));
      if (p) return p;
    }
  } else if (isPlainObject(a) && isPlainObject(b)) {
    // Both are non-array objects
    const keys = Array.from(new Set([...Object.keys(a), ...Object.keys(b)])).sort();
    for (const k of keys) {
      if (!(k in a) || !(k in b)) return path(k);
      const p = diffPath(a[k], b[k], path(k));
      if (p) return p;
    }
  } else {
    return base || "/";
  }

  return null;
}

export function equals(actual: unknown, expected: unknown): OracleResult {
  const p = diffPath(actual, expected, "");
  if (p === null) return { ok: true };
  const code = "E_NOT_EQUAL" as const;
  return { ok: false, code, message: MESSAGES[code](), path: p };
}
