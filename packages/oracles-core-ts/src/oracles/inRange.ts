import type { OracleResult } from "../result.js";

export function inRange(actual: unknown, min: number, max: number): OracleResult {
  if (
    typeof actual !== "number" ||
    Number.isNaN(actual) ||
    actual < min ||
    actual > max
  ) {
    return {
      ok: false,
      code: "E_OUT_OF_RANGE",
      message: "value is out of range",
      path: "/",
      evidence: { min, max, actual },
    };
  }
  return { ok: true };
}

