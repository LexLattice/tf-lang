import type { OracleResult } from "../result.js";

export function matchesRegex(actual: unknown, pattern: RegExp): OracleResult {
  if (typeof actual !== "string") {
    return { ok: false, code: "E_REGEX_MISMATCH", message: "value does not match regex", path: "/", evidence: { pattern: String(pattern) } };
  }
  if (!pattern.test(actual)) {
    return { ok: false, code: "E_REGEX_MISMATCH", message: "value does not match regex", path: "/", evidence: { pattern: String(pattern), actual } };
  }
  return { ok: true };
}

