import { err, ok, withTrace } from "@tf/oracles-core";
import type { Oracle, OracleCtx, OracleResult } from "@tf/oracles-core";

import type {
  IdempotenceApplication,
  IdempotenceCase,
  IdempotenceInput,
  IdempotenceMismatch,
  IdempotenceReport,
} from "./types.js";

export type { IdempotenceApplication, IdempotenceCase, IdempotenceInput, IdempotenceMismatch, IdempotenceReport } from "./types.js";

const FAILURE_CODE = "E_NOT_IDEMPOTENT" as const;
const MISSING_VALUE = "[missing]" as const;

export function createIdempotenceOracle(): Oracle<IdempotenceInput, IdempotenceReport> {
  return {
    async check(input, ctx) {
      return checkIdempotence(input, ctx);
    },
  };
}

export async function checkIdempotence(
  input: IdempotenceInput,
  ctx: OracleCtx,
): Promise<OracleResult<IdempotenceReport>> {
  const cases = input.cases ?? [];
  let casesChecked = 0;
  let applicationsChecked = 0;
  const mismatches: IdempotenceMismatch[] = [];

  for (const idempotenceCase of cases) {
    casesChecked += 1;
    const applications = canonicalizeApplications(idempotenceCase.applications ?? [], ctx);
    if (applications.length <= 1) {
      continue;
    }
    const baseline = applications[0];
    for (let index = 1; index < applications.length; index += 1) {
      applicationsChecked += 1;
      const candidate = applications[index];
      const diff = diffValues(baseline.value, candidate.value);
      if (diff) {
        mismatches.push({
          case: idempotenceCase.name,
          seed: idempotenceCase.seed,
          iteration: candidate.iteration,
          pointer: diff.pointer,
          expected: diff.left,
          actual: diff.right,
        });
      }
    }
  }

  if (mismatches.length > 0) {
    const trace = mismatches.slice(0, 5).map((item) => `case:${item.case}:iteration:${item.iteration}`);
    const failure = err(FAILURE_CODE, "Repeated application diverged", { mismatches });
    return withTrace(failure, trace);
  }

  return ok({ casesChecked, applicationsChecked });
}

interface CanonicalApplication {
  readonly iteration: number;
  readonly value: unknown;
}

function canonicalizeApplications(
  applications: ReadonlyArray<IdempotenceApplication>,
  ctx: OracleCtx,
): CanonicalApplication[] {
  return applications.map((application, index) => ({
    iteration: application.iteration ?? index,
    value: ctx.canonicalize(application.value),
  }));
}

interface DiffResult {
  readonly pointer: string;
  readonly left: unknown;
  readonly right: unknown;
}

function diffValues(left: unknown, right: unknown, segments: Array<string | number> = []): DiffResult | null {
  if (Object.is(left, right)) {
    return null;
  }

  if (left === null || right === null) {
    if (left === right) {
      return null;
    }
    return {
      pointer: pointerFromSegments(segments),
      left,
      right,
    };
  }

  if (Array.isArray(left) || Array.isArray(right)) {
    if (!Array.isArray(left) || !Array.isArray(right)) {
      return {
        pointer: pointerFromSegments(segments),
        left,
        right,
      };
    }
    const max = Math.min(left.length, right.length);
    for (let index = 0; index < max; index += 1) {
      const child = diffValues(left[index] ?? null, right[index] ?? null, [...segments, index]);
      if (child) {
        return child;
      }
    }
    if (left.length !== right.length) {
      const pointer = pointerFromSegments([...segments, max]);
      const missingLeft = left.length > right.length ? left[max] ?? null : MISSING_VALUE;
      const missingRight = right.length > left.length ? right[max] ?? null : MISSING_VALUE;
      return {
        pointer,
        left: missingLeft,
        right: missingRight,
      };
    }
    return null;
  }

  if (isPlainObject(left) || isPlainObject(right)) {
    if (!isPlainObject(left) || !isPlainObject(right)) {
      return {
        pointer: pointerFromSegments(segments),
        left,
        right,
      };
    }
    const keys = Array.from(new Set([...Object.keys(left), ...Object.keys(right)])).sort();
    for (const key of keys) {
      const hasLeft = Object.prototype.hasOwnProperty.call(left, key);
      const hasRight = Object.prototype.hasOwnProperty.call(right, key);
      if (!hasLeft || !hasRight) {
        return {
          pointer: pointerFromSegments([...segments, key]),
          left: hasLeft ? (left as Record<string, unknown>)[key] : MISSING_VALUE,
          right: hasRight ? (right as Record<string, unknown>)[key] : MISSING_VALUE,
        };
      }
      const child = diffValues(
        (left as Record<string, unknown>)[key],
        (right as Record<string, unknown>)[key],
        [...segments, key],
      );
      if (child) {
        return child;
      }
    }
    return null;
  }

  return {
    pointer: pointerFromSegments(segments),
    left,
    right,
  };
}

function pointerFromSegments(segments: Array<string | number>): string {
  if (segments.length === 0) {
    return "/";
  }
  return `/${segments.map(escapePointerSegment).join("/")}`;
}

function escapePointerSegment(segment: string | number): string {
  return String(segment).replace(/~/g, "~0").replace(/\//g, "~1");
}

function isPlainObject(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}
