import type { OracleResult } from "../result.js";

function diffPath(a: any, b: any, base: string = ""): string | null {
  const path = (k: string | number) =>
    base + "/" + String(k).replace(/~/g, "~0").replace(/\//g, "~1");
  if (Object.is(a, b)) return null;

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
  } else {
    // Both are non-array objects
    const keys = Array.from(new Set([...Object.keys(a), ...Object.keys(b)])).sort();
    for (const k of keys) {
      if (!(k in a) || !(k in b)) return path(k);
      const p = diffPath(a[k], b[k], path(k));
      if (p) return p;
    }
  }

  return null;
}

export function equals(actual: unknown, expected: unknown): OracleResult {
  const p = diffPath(actual, expected, "");
  if (p === null) return { ok: true };
  return { ok: false, code: "E_NOT_EQUAL", message: "values are not equal", path: p };
}

