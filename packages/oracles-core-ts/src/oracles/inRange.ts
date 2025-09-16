import type { OracleResult } from "../result.js";
import { MESSAGES } from "../messages.js";

export function inRange(actual: unknown, min: number, max: number): OracleResult {
  if (
    typeof actual !== "number" ||
    Number.isNaN(actual) ||
    actual < min ||
    actual > max
  ) {
    const code = "E_OUT_OF_RANGE" as const;
    return {
      ok: false,
      code,
      message: MESSAGES[code]({ min, max }),
      path: "/",
      evidence: { min, max, actual },
    };
  }
  return { ok: true };
}
