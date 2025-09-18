import { err, ok, withTrace } from "@tf/oracles-core";
import type { Oracle, OracleCtx, OracleResult } from "@tf/oracles-core";

import type { TransportDrift, TransportInput, TransportReport } from "./types.js";

export type { TransportDrift, TransportInput, TransportReport } from "./types.js";

const FAILURE_CODE = "E_TRANSPORT_DRIFT" as const;
const UNSERIALIZABLE = "[unserializable]" as const;
const INVALID_JSON = "[invalid-json]" as const;
const MISSING_VALUE = "[missing]" as const;

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
  const cases = input.cases ?? [];
  const drifts: TransportDrift[] = [];

  let roundTripsChecked = 0;

  for (const transportCase of cases) {
    roundTripsChecked += 1;

    const original = ctx.canonicalize(transportCase.value);
    const serialization =
      transportCase.encoded !== undefined
        ? ({ ok: true as const, value: transportCase.encoded } satisfies SerializeSuccess)
        : serializeValue(transportCase.value);

    if (!serialization.ok) {
      drifts.push({
        case: transportCase.name,
        seed: transportCase.seed,
        pointer: pointerFromSegments([]),
        before: original,
        after: UNSERIALIZABLE,
      });
      continue;
    }

    const parsed = parseJson(serialization.value);
    if (!parsed.ok) {
      drifts.push({
        case: transportCase.name,
        seed: transportCase.seed,
        pointer: pointerFromSegments([]),
        before: original,
        after: INVALID_JSON,
      });
      continue;
    }

    const normalized = ctx.canonicalize(parsed.value);
    const diff = diffValues(original, normalized);
    if (diff) {
      drifts.push({
        case: transportCase.name,
        seed: transportCase.seed,
        pointer: diff.pointer,
        before: diff.left,
        after: diff.right,
      });
    }
  }

  if (drifts.length > 0) {
    const trace = drifts.slice(0, 5).map((drift) => `case:${drift.case}:${drift.pointer}`);
    const failure = err(FAILURE_CODE, "Transport round-trip drift detected", { drifts });
    return withTrace(failure, trace);
  }

  return ok({ casesChecked: cases.length, roundTripsChecked });
}

interface SerializeSuccess {
  readonly ok: true;
  readonly value: string;
}

type SerializeResult = SerializeSuccess | { readonly ok: false };

function serializeValue(value: unknown): SerializeResult {
  try {
    const result = JSON.stringify(value);
    if (typeof result !== "string") {
      return { ok: false };
    }
    return { ok: true, value: result };
  } catch {
    return { ok: false };
  }
}

type ParseResult = { readonly ok: true; readonly value: unknown } | { readonly ok: false };

function parseJson(value: string): ParseResult {
  try {
    return { ok: true, value: JSON.parse(value) };
  } catch {
    return { ok: false };
  }
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
