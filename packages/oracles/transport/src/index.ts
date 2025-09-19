import { diffCanonical, err, ok, pointerFromSegments, withTrace } from "@tf/oracles-core";
import type { Oracle, OracleCtx, OracleResult } from "@tf/oracles-core";

import type { TransportDrift, TransportInput, TransportReport } from "./types.js";

export type { TransportDrift, TransportInput, TransportReport, TransportIssue } from "./types.js";

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
        ? ensurePreEncoded(transportCase.encoded)
        : serializeValue(transportCase.value);

    if (!serialization.ok) {
      drifts.push({
        case: transportCase.name,
        seed: transportCase.seed,
        pointer: pointerFromSegments([]),
        before: original,
        after: UNSERIALIZABLE,
        issue: serialization,
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
        issue: parsed,
      });
      continue;
    }

    const normalized = ctx.canonicalize(parsed.value);
    const diff = diffCanonical(original, normalized, { missingValue: MISSING_VALUE });
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
  readonly code: "E_TRANSPORT_SERIALIZE";
  readonly message: string;
}

type SerializeResult = SerializeSuccess | SerializeFailure;

function ensurePreEncoded(encoded: unknown): SerializeResult {
  if (typeof encoded !== "string") {
    return { ok: false, code: "E_TRANSPORT_SERIALIZE", message: "pre-encoded payload must be a string" };
  }
  return { ok: true, value: encoded };
}

function serializeValue(value: unknown): SerializeResult {
  if (containsMap(value)) {
    // Treat Maps as unsupported for JSON round-trips so drift is recorded deterministically.
    return { ok: false, code: "E_TRANSPORT_SERIALIZE", message: "Map values are not JSON-serializable" };
  }
  try {
    const result = JSON.stringify(value);
    if (typeof result !== "string") {
      return { ok: false, code: "E_TRANSPORT_SERIALIZE", message: "JSON.stringify returned a non-string" };
    }
    return { ok: true, value: result };
  } catch (error) {
    return {
      ok: false,
      code: "E_TRANSPORT_SERIALIZE",
      message: error instanceof Error ? error.message : "Unknown serialization error",
    };
  }
}

interface ParseSuccess {
  readonly ok: true;
  readonly value: unknown;
}

interface ParseFailure {
  readonly ok: false;
  readonly code: "E_TRANSPORT_DECODE";
  readonly message: string;
}

type ParseResult = ParseSuccess | ParseFailure;

function parseJson(value: string): ParseResult {
  try {
    return { ok: true, value: JSON.parse(value) };
  } catch (error) {
    return {
      ok: false,
      code: "E_TRANSPORT_DECODE",
      message: error instanceof Error ? error.message : "Unknown decode error",
    };
  }
}

function containsMap(value: unknown, seen: Set<unknown> = new Set()): boolean {
  if (value === null || typeof value !== "object") {
    return false;
  }
  if (seen.has(value)) {
    return false;
  }
  if (value instanceof Map) {
    return true;
  }

  seen.add(value);

  if (value instanceof Set) {
    for (const entry of value.values()) {
      if (containsMap(entry, seen)) {
        return true;
      }
    }
    return false;
  }

  if (Array.isArray(value)) {
    for (const entry of value) {
      if (containsMap(entry, seen)) {
        return true;
      }
    }
    return false;
  }

  for (const entry of Object.values(value as Record<string, unknown>)) {
    if (containsMap(entry, seen)) {
      return true;
    }
  }

  return false;
}
