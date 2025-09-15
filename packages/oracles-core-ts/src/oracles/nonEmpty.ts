import type { OracleResult } from "../result.js";

export function nonEmpty(actual: unknown): OracleResult {
  if (typeof actual === "string") {
    return actual.length > 0 ? { ok: true } : { ok: false, code: "E_EMPTY", message: "value is empty", path: "/" };
  }
  if (Array.isArray(actual)) {
    return actual.length > 0 ? { ok: true } : { ok: false, code: "E_EMPTY", message: "value is empty", path: "/" };
  }
  return { ok: false, code: "E_EMPTY", message: "value is empty", path: "/" };
}

