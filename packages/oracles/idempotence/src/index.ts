import { err, ok, withTrace } from "@tf/oracles-core";
import { canonicalStringify } from "@tf/oracles-core";
import type { Oracle, OracleCtx, OracleResult } from "@tf/oracles-core";

import type { IdempotenceInput, IdempotenceMismatch, IdempotenceReport } from "./types.js";

export type { IdempotenceCase, IdempotenceInput, IdempotenceReport } from "./types.js";

const FAILURE_CODE = "E_NON_IDEMPOTENT";

export function createIdempotenceOracle(): Oracle<IdempotenceInput, IdempotenceReport> {
  return {
    async check(input: IdempotenceInput, ctx: OracleCtx) {
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
  const mismatches: IdempotenceMismatch[] = [];

  for (const idempotenceCase of cases) {
    casesChecked += 1;
    const canonicalOnce = ctx.canonicalize(idempotenceCase.once ?? null);
    const canonicalTwice = ctx.canonicalize(idempotenceCase.twice ?? null);

    const mismatch = findFirstMismatch(canonicalOnce, canonicalTwice);
    if (mismatch) {
      mismatches.push({
        case: idempotenceCase.name,
        pointer: mismatch.pointer,
        once: mismatch.once,
        twice: mismatch.twice,
      });
    }
  }

  if (mismatches.length > 0) {
    const failure = err(FAILURE_CODE, "Idempotence violations detected", { mismatches });
    const trace = mismatches
      .slice(0, 5)
      .map((entry) => `case:${entry.case}${entry.pointer}`);
    return withTrace(failure, trace);
  }

  return ok({ casesChecked, mismatches: [] });
}

interface MismatchDetail {
  readonly pointer: string;
  readonly once: unknown;
  readonly twice: unknown;
}

function findFirstMismatch(left: unknown, right: unknown): MismatchDetail | undefined {
  if (canonicalStringify(left) === canonicalStringify(right)) {
    return undefined;
  }

  if (Array.isArray(left) && Array.isArray(right)) {
    const maxLength = Math.max(left.length, right.length);
    for (let index = 0; index < maxLength; index += 1) {
      if (index >= left.length) {
        return {
          pointer: pointerFromSegments([index]),
          once: undefined,
          twice: right[index],
        };
      }
      if (index >= right.length) {
        return {
          pointer: pointerFromSegments([index]),
          once: left[index],
          twice: undefined,
        };
      }
      const nested = findFirstMismatch(left[index], right[index]);
      if (nested) {
        return {
          pointer: pointerFromSegments([index, ...segmentsFromPointer(nested.pointer)]),
          once: nested.once,
          twice: nested.twice,
        };
      }
    }
    return undefined;
  }

  if (isPlainObject(left) && isPlainObject(right)) {
    const keys = new Set<string>([...Object.keys(left), ...Object.keys(right)]);
    const sorted = Array.from(keys).sort();
    for (const key of sorted) {
      if (!(key in left)) {
        return {
          pointer: pointerFromSegments([key]),
          once: undefined,
          twice: right[key],
        };
      }
      if (!(key in right)) {
        return {
          pointer: pointerFromSegments([key]),
          once: left[key],
          twice: undefined,
        };
      }
      const nested = findFirstMismatch(left[key], right[key]);
      if (nested) {
        return {
          pointer: pointerFromSegments([key, ...segmentsFromPointer(nested.pointer)]),
          once: nested.once,
          twice: nested.twice,
        };
      }
    }
    return undefined;
  }

  return { pointer: pointerFromSegments([]), once: left, twice: right };
}

function isPlainObject(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

function pointerFromSegments(segments: ReadonlyArray<string | number>): string {
  if (segments.length === 0) {
    return "/";
  }
  const encoded = segments.map((segment) => encodePointerSegment(String(segment)));
  return `/${encoded.join("/")}`;
}

function encodePointerSegment(segment: string): string {
  return segment.replace(/~/g, "~0").replace(/\//g, "~1");
}

function segmentsFromPointer(pointer: string): ReadonlyArray<string | number> {
  if (pointer === "/" || pointer === "") {
    return [];
  }
  const segments = pointer.split("/").slice(1);
  return segments.map((segment) => segment.replace(/~1/g, "/").replace(/~0/g, "~"));
}
