import type { OracleResult } from "../result.js";

export function subsetOf(actual: unknown, expected: unknown): OracleResult {
  if (!actual || typeof actual !== "object" || !expected || typeof expected !== "object") {
    return { ok: false, code: "E_NOT_SUBSET", message: "object is not a subset of expected", path: "/" };
  }
  const a = actual as Record<string, unknown>;
  const e = expected as Record<string, unknown>;
  for (const k of Object.keys(a).sort()) {
    if (!(k in e)) return { ok: false, code: "E_FIELD_UNKNOWN", message: "unknown field present", path: `/${k}` };
    const av = a[k];
    const ev = e[k];
    if (av && typeof av === "object" && ev && typeof ev === "object") {
      const r = subsetOf(av, ev);
      if (!r.ok) return { ...r, path: `/${k}${r.path!}` };
    } else if (!Object.is(av, ev)) {
      return { ok: false, code: "E_NOT_SUBSET", message: "object is not a subset of expected", path: `/${k}` };
    }
  }
  return { ok: true };
}

