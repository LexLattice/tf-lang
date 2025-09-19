import {
  diffValues as diffValuesCore,
  pointerFromSegments,
  type DiffResult,
  err,
  ok,
  withTrace,
} from "@tf/oracles-core";
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

    const unsupported = findUnsupportedValue(transportCase.value, new Set());
    const original = unsupported ? UNSERIALIZABLE : ctx.canonicalize(transportCase.value);
    if (unsupported) {
      drifts.push({
        case: transportCase.name,
        seed: transportCase.seed,
        pointer: pointerFromSegments([]),
        before: original,
        after: UNSERIALIZABLE,
        error: {
          code: SERIALIZE_ERROR_CODE,
          message: unsupported,
        },
      });
      continue;
    }
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
        error: serialization.error,
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
        error: parsed.error,
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

interface SerializeFailure {
  readonly ok: false;
  readonly error: {
    readonly code: typeof SERIALIZE_ERROR_CODE;
    readonly message: string;
  };
}

type SerializeResult = SerializeSuccess | SerializeFailure;

const SERIALIZE_ERROR_CODE = "E_TRANSPORT_SERIALIZE" as const;
const DECODE_ERROR_CODE = "E_TRANSPORT_DECODE" as const;

function serializeValue(value: unknown): SerializeResult {
  const unsupported = findUnsupportedValue(value, new Set());
  if (unsupported) {
    return {
      ok: false,
      error: {
        code: SERIALIZE_ERROR_CODE,
        message: unsupported,
      },
    };
  }

  try {
    const result = JSON.stringify(value);
    if (typeof result !== "string") {
      return {
        ok: false,
        error: {
          code: SERIALIZE_ERROR_CODE,
          message: "JSON.stringify did not return a string",
        },
      };
    }
    return { ok: true, value: result };
  } catch (error) {
    return {
      ok: false,
      error: {
        code: SERIALIZE_ERROR_CODE,
        message: error instanceof Error ? error.message : "Unknown serialization error",
      },
    };
  }
}

type ParseResult =
  | { readonly ok: true; readonly value: unknown }
  | { readonly ok: false; readonly error: { readonly code: typeof DECODE_ERROR_CODE; readonly message: string } };

function parseJson(encoded: unknown): ParseResult {
  if (typeof encoded !== "string") {
    return {
      ok: false,
      error: { code: DECODE_ERROR_CODE, message: "Encoded payload must be a string" },
    };
  }

  try {
    return { ok: true, value: JSON.parse(encoded) };
  } catch (error) {
    return {
      ok: false,
      error: {
        code: DECODE_ERROR_CODE,
        message: error instanceof Error ? error.message : "Unknown JSON parse error",
      },
    };
  }
}

function diffValues(left: unknown, right: unknown): DiffResult | null {
  return diffValuesCore(left, right, { missingValue: MISSING_VALUE });
}

function findUnsupportedValue(value: unknown, seen: Set<unknown>): string | null {
  if (value === null) {
    return null;
  }

  const valueType = typeof value;
  if (valueType === "bigint") {
    return "BigInt values are not supported";
  }

  if (valueType !== "object") {
    return null;
  }

  if (seen.has(value)) {
    return "Cyclic structures are not supported";
  }

  seen.add(value);

  if (value instanceof Map) {
    return "Map values are not supported";
  }

  if (value instanceof Set) {
    for (const entry of value) {
      const result = findUnsupportedValue(entry, seen);
      if (result) {
        return result;
      }
    }
    seen.delete(value);
    return null;
  }

  if (Array.isArray(value)) {
    for (const entry of value) {
      const result = findUnsupportedValue(entry, seen);
      if (result) {
        return result;
      }
    }
    seen.delete(value);
    return null;
  }

  const prototype = Object.getPrototypeOf(value);
  if (prototype === null || prototype === Object.prototype) {
    for (const key of Object.keys(value as Record<string, unknown>)) {
      const entry = (value as Record<string, unknown>)[key];
      if (entry === undefined) {
        continue;
      }
      const result = findUnsupportedValue(entry, seen);
      if (result) {
        return result;
      }
    }
    seen.delete(value);
    return null;
  }

  // Non-plain objects without special handling fall back to JSON.stringify semantics.
  seen.delete(value);
  return null;
}
