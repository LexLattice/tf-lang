import type { OracleResult } from "../result.js";
import { MESSAGES } from "../messages.js";

export function nonEmpty(actual: unknown): OracleResult {
  if (typeof actual === "string" || Array.isArray(actual)) {
    if (actual.length > 0) return { ok: true };
  }
  const code = "E_EMPTY" as const;
  return { ok: false, code, message: MESSAGES[code](), path: "/" };
}
