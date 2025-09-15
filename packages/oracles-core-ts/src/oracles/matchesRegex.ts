import type { OracleResult } from "../result.js";
import { MESSAGES } from "../messages.js";

export function matchesRegex(actual: unknown, pattern: RegExp): OracleResult {
  if (typeof actual !== "string") {
    const code = "E_REGEX_MISMATCH" as const;
    return { ok: false, code, message: MESSAGES[code]({ pattern: String(pattern) }), path: "/", evidence: { pattern: String(pattern) } };
  }
  if (pattern.global || pattern.sticky) pattern.lastIndex = 0;
  if (!pattern.test(actual)) {
    const code = "E_REGEX_MISMATCH" as const;
    return { ok: false, code, message: MESSAGES[code]({ pattern: String(pattern) }), path: "/", evidence: { pattern: String(pattern), actual } };
  }
  return { ok: true };
}
