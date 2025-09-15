import type { OracleResult } from "../result.js";

export function nonEmpty(actual: unknown): OracleResult {
  if (typeof actual === "string" || Array.isArray(actual)) {
    if (actual.length > 0) return { ok: true };
  }
  return { ok: false, code: "E_EMPTY", message: "value is empty", path: "/" };
}

