import type { OracleResult } from "../result.js";
import { MESSAGES } from "../messages.js";

function escapePointerSegment(segment: string | number): string {
  return String(segment).replace(/~/g, "~0").replace(/\//g, "~1");
}

function pointerFromSegments(segments: Array<string | number>): string {
  if (segments.length === 0) return "/";
  return `/${segments.map(escapePointerSegment).join("/")}`;
}

function subsetOfInner(actual: unknown, expected: unknown, segments: Array<string | number>): OracleResult {
  if (!actual || typeof actual !== "object" || !expected || typeof expected !== "object") {
    const code = "E_NOT_SUBSET" as const;
    return { ok: false, code, message: MESSAGES[code](), path: pointerFromSegments(segments) };
  }
  const a = actual as Record<string, unknown>;
  const e = expected as Record<string, unknown>;
  for (const k of Object.keys(a).sort()) {
    if (!(k in e)) {
      return { ok: false, code: "E_FIELD_UNKNOWN", message: "unknown field present", path: pointerFromSegments([...segments, k]) };
    }
    const av = a[k];
    const ev = e[k];
    if (av && typeof av === "object" && ev && typeof ev === "object") {
      const result = subsetOfInner(av, ev, [...segments, k]);
      if (!result.ok) return result;
    } else if (!Object.is(av, ev)) {
      const code = "E_NOT_SUBSET" as const;
      return { ok: false, code, message: MESSAGES[code](), path: pointerFromSegments([...segments, k]) };
    }
  }
  return { ok: true };
}

export function subsetOf(actual: unknown, expected: unknown): OracleResult {
  return subsetOfInner(actual, expected, []);
}
