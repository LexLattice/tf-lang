import { canonicalStringify, err, ok, withTrace } from "@tf/oracles-core";
import type { Oracle, OracleCtx, OracleResult } from "@tf/oracles-core";

import type {
  ConservationInput,
  ConservationReport,
  ConservationViolation,
} from "./types.js";

export type { ConservationInput, ConservationReport, ConservationViolation } from "./types.js";

const FAILURE_CODE = "E_NOT_CONSERVED" as const;
const MISSING_VALUE = "[missing]" as const;

export function createConservationOracle(): Oracle<ConservationInput, ConservationReport> {
  return {
    async check(input, ctx) {
      return checkConservation(input, ctx);
    },
  };
}

export async function checkConservation(
  input: ConservationInput,
  ctx: OracleCtx,
): Promise<OracleResult<ConservationReport>> {
  const before = canonicalizeSnapshot(input.before, ctx);
  const after = canonicalizeSnapshot(input.after, ctx);
  const keys = collectKeys(input.keys, before, after);

  const violations: ConservationViolation[] = [];

  for (const key of keys) {
    const hasBefore = Object.prototype.hasOwnProperty.call(before, key);
    const hasAfter = Object.prototype.hasOwnProperty.call(after, key);
    const beforeValue = hasBefore ? before[key] : MISSING_VALUE;
    const afterValue = hasAfter ? after[key] : MISSING_VALUE;

    if (!valuesEqual(beforeValue, afterValue)) {
      violations.push({
        key,
        before: beforeValue,
        after: afterValue,
        delta: computeDelta(beforeValue, afterValue),
      });
    }
  }

  if (violations.length > 0) {
    const trace = violations.slice(0, 5).map((violation) => `key:${violation.key}`);
    const failure = err(FAILURE_CODE, "Conservation violated", { violations });
    return withTrace(failure, trace);
  }

  return ok({ keysChecked: keys.length });
}

type Snapshot = Record<string, unknown>;

function canonicalizeSnapshot(snapshot: Record<string, unknown> | undefined, ctx: OracleCtx): Snapshot {
  if (!snapshot || typeof snapshot !== "object") {
    return {};
  }
  const result: Snapshot = {};
  for (const [key, value] of Object.entries(snapshot)) {
    if (value === undefined) {
      continue;
    }
    result[key] = ctx.canonicalize(value ?? null);
  }
  return result;
}

function collectKeys(
  declared: ReadonlyArray<string> | undefined,
  before: Snapshot,
  after: Snapshot,
): string[] {
  const result = new Set<string>();
  if (declared && declared.length > 0) {
    for (const key of declared) {
      if (typeof key === "string" && key.length > 0) {
        result.add(key);
      }
    }
  } else {
    for (const key of Object.keys(before)) {
      result.add(key);
    }
    for (const key of Object.keys(after)) {
      result.add(key);
    }
  }
  return Array.from(result).sort();
}

function valuesEqual(left: unknown, right: unknown): boolean {
  if (Object.is(left, right)) {
    return true;
  }
  if (typeof left === "object" || typeof right === "object") {
    return canonicalStringify(left) === canonicalStringify(right);
  }
  return false;
}

function computeDelta(left: unknown, right: unknown): number | null {
  if (typeof left !== "number" || typeof right !== "number") {
    return null;
  }
  if (!Number.isFinite(left) || !Number.isFinite(right)) {
    return null;
  }
  const raw = right - left;
  const formatted = Number.parseFloat(raw.toFixed(12));
  return Object.is(formatted, -0) ? 0 : formatted;
}
