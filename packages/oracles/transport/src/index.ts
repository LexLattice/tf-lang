import { canonicalStringify, err, ok, withTrace } from "@tf/oracles-core";
import type { Oracle, OracleCtx, OracleResult } from "@tf/oracles-core";

import type {
  TransportCase,
  TransportInput,
  TransportMismatch,
  TransportReport,
} from "./types.js";

export type { TransportCase, TransportInput, TransportMismatch, TransportReport } from "./types.js";

const FAILURE_CODE = "E_TRANSPORT_DIVERGED" as const;
const MISSING_VALUE = "[missing]" as const;
const UNSERIALIZABLE_VALUE = "[unserializable]" as const;

export function createTransportOracle(): Oracle<TransportInput, TransportReport> {
  return {
    async check(input, ctx) {
      return checkTransport(input, ctx);
    },
  };
}

export async function checkTransport(
  input: TransportInput,
  ctx: OracleCtx,
): Promise<OracleResult<TransportReport>> {
  const cases = normalizeCases(input);
  let casesChecked = 0;
  let roundTripsChecked = 0;
  const mismatches: TransportMismatch[] = [];

  for (const transportCase of cases) {
    casesChecked += 1;
    const { value, name, seed } = transportCase;

    if (value === undefined) {
      mismatches.push({
        case: name,
        seed,
        pointer: "",
        expected: MISSING_VALUE,
        actual: MISSING_VALUE,
      });
      continue;
    }

    const canonicalBefore = ctx.canonicalize(value ?? null);
    const serialized = JSON.stringify(value);
    if (serialized === undefined) {
      mismatches.push({
        case: name,
        seed,
        pointer: "",
        expected: canonicalBefore,
        actual: UNSERIALIZABLE_VALUE,
      });
      continue;
    }

    let parsed: unknown;
    try {
      parsed = JSON.parse(serialized);
    } catch (error) {
      mismatches.push({
        case: name,
        seed,
        pointer: "",
        expected: serialized,
        actual: error instanceof Error ? error.message : String(error),
      });
      continue;
    }

    roundTripsChecked += 1;
    const canonicalAfter = ctx.canonicalize(parsed ?? null);
    const diff = diffValues(canonicalBefore, canonicalAfter);
    if (diff) {
      mismatches.push({
        case: name,
        seed,
        pointer: diff.pointer,
        expected: diff.left,
        actual: diff.right,
      });
    }
  }

  if (mismatches.length > 0) {
    const trace = mismatches
      .slice(0, 5)
      .map((item) => `case:${item.case ?? "unknown"}:pointer:${item.pointer || "root"}`);
    const failure = err(FAILURE_CODE, "Transport round-trip diverged", { mismatches });
    return withTrace(failure, trace);
  }

  return ok({ casesChecked, roundTripsChecked });
}

function normalizeCases(input: TransportInput): TransportCase[] {
  if (Array.isArray(input.cases) && input.cases.length > 0) {
    return input.cases.map((entry, index) => ({
      name: entry?.name ?? `case:${index}`,
      seed: entry?.seed,
      value: entry?.value,
    }));
  }

  if (Object.prototype.hasOwnProperty.call(input, "value")) {
    return [
      {
        name: "case:0",
        seed: undefined,
        value: (input as { value: unknown }).value,
      },
    ];
  }

  return [];
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
      const missingLeft = left.length > right.length ? left[max] ?? MISSING_VALUE : MISSING_VALUE;
      const missingRight = right.length > left.length ? right[max] ?? MISSING_VALUE : MISSING_VALUE;
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
          left: hasLeft ? (left as Record<string, unknown>)[key] ?? MISSING_VALUE : MISSING_VALUE,
          right: hasRight ? (right as Record<string, unknown>)[key] ?? MISSING_VALUE : MISSING_VALUE,
        };
      }

      const child = diffValues(
        (left as Record<string, unknown>)[key] ?? null,
        (right as Record<string, unknown>)[key] ?? null,
        [...segments, key],
      );
      if (child) {
        return child;
      }
    }

    return null;
  }

  const pointer = pointerFromSegments(segments);
  if (canonicalStringify(left) === canonicalStringify(right)) {
    return null;
  }

  return {
    pointer,
    left,
    right,
  };
}

function pointerFromSegments(segments: Array<string | number>): string {
  if (segments.length === 0) {
    return "";
  }
  return `/${segments.map(escapePointerSegment).join("/")}`;
}

function escapePointerSegment(segment: string | number): string {
  return String(segment).replace(/~/g, "~0").replace(/\//g, "~1");
}

function isPlainObject(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}
