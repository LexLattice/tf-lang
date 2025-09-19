import {
  diffCanonical,
  err,
  ok,
  pointerFromSegments,
  withTrace,
} from "@tf/oracles-core";
import type { Oracle, OracleCtx, OracleResult } from "@tf/oracles-core";

import type { TransportDrift, TransportInput, TransportReport } from "./types.js";

export type { TransportDrift, TransportInput, TransportReport } from "./types.js";

const FAILURE_CODE = "E_TRANSPORT_DRIFT" as const;
const SERIALIZE_FAILURE_CODE = "E_TRANSPORT_SERIALIZE" as const;
const DECODE_FAILURE_CODE = "E_TRANSPORT_DECODE" as const;
const UNSERIALIZABLE = "[unserializable]" as const;
const INVALID_JSON = "[invalid-json]" as const;
const CYCLE_VALUE = "[cycle]" as const;
const FAILURE_MESSAGES: Record<string, string> = {
  [FAILURE_CODE]: "Transport round-trip drift detected",
  [SERIALIZE_FAILURE_CODE]: "Transport value could not be serialized",
  [DECODE_FAILURE_CODE]: "Transport payload could not be decoded",
};
const MAP_SERIALIZE_MESSAGE = "Encountered Map value which cannot round-trip through JSON";
const CYCLE_SERIALIZE_MESSAGE = "Encountered cyclic value which cannot round-trip through JSON";

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
  let failureCode: string | null = null;
  let failureMessage: string | null = null;

  for (const transportCase of cases) {
    roundTripsChecked += 1;

    const mapIssue = findFirstMap(transportCase.value);
    if (mapIssue) {
      if (failureCode !== SERIALIZE_FAILURE_CODE) {
        failureCode = SERIALIZE_FAILURE_CODE;
        failureMessage = MAP_SERIALIZE_MESSAGE;
      }
      drifts.push({
        case: transportCase.name,
        seed: transportCase.seed,
        pointer: pointerFromSegments(mapIssue.path),
        before: canonicalizeMapForReport(mapIssue.map, ctx),
        after: UNSERIALIZABLE,
      });
      continue;
    }

    const cycleIssue = findFirstCycle(transportCase.value);
    if (cycleIssue) {
      if (failureCode !== SERIALIZE_FAILURE_CODE) {
        failureCode = SERIALIZE_FAILURE_CODE;
        failureMessage = CYCLE_SERIALIZE_MESSAGE;
      }
      drifts.push({
        case: transportCase.name,
        seed: transportCase.seed,
        pointer: pointerFromSegments(cycleIssue.path),
        before: CYCLE_VALUE,
        after: UNSERIALIZABLE,
      });
      continue;
    }

    const original = ctx.canonicalize(transportCase.value);

    const serialization =
      transportCase.encoded !== undefined
        ? usePreEncoded(transportCase.encoded)
        : serializeValue(transportCase.value);

    if (!serialization.ok) {
      if (failureCode !== SERIALIZE_FAILURE_CODE) {
        failureCode = SERIALIZE_FAILURE_CODE;
        failureMessage = serialization.message;
      } else if (!failureMessage) {
        failureMessage = serialization.message;
      }
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
      if (failureCode !== SERIALIZE_FAILURE_CODE) {
        if (failureCode !== DECODE_FAILURE_CODE) {
          failureCode = DECODE_FAILURE_CODE;
          failureMessage = parsed.message;
        } else if (!failureMessage) {
          failureMessage = parsed.message;
        }
      }
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
    const diff = diffCanonical(original, normalized);
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
    const code = failureCode ?? FAILURE_CODE;
    const explain = failureMessage ?? FAILURE_MESSAGES[code] ?? FAILURE_MESSAGES[FAILURE_CODE];
    const failure = err(code, explain, { drifts });
    return withTrace(failure, trace);
  }

  return ok({ casesChecked: cases.length, roundTripsChecked });
}

type SerializeSuccess = { readonly ok: true; readonly value: string };
type SerializeFailure = { readonly ok: false; readonly message: string };
type SerializeResult = SerializeSuccess | SerializeFailure;

function usePreEncoded(encoded: unknown): SerializeResult {
  if (typeof encoded !== "string") {
    return { ok: false, message: "Pre-encoded payload must be a string" };
  }
  return { ok: true, value: encoded };
}

function serializeValue(value: unknown): SerializeResult {
  try {
    const result = JSON.stringify(value);
    if (typeof result !== "string") {
      return { ok: false, message: "JSON.stringify returned a non-string result" };
    }
    return { ok: true, value: result };
  } catch (error) {
    const message = error instanceof Error ? error.message : "Unknown serialization error";
    return { ok: false, message };
  }
}

type ParseSuccess = { readonly ok: true; readonly value: unknown };
type ParseFailure = { readonly ok: false; readonly message: string };
type ParseResult = ParseSuccess | ParseFailure;

function parseJson(value: string): ParseResult {
  try {
    return { ok: true, value: JSON.parse(value) };
  } catch (error) {
    const message = error instanceof Error ? error.message : "Unknown JSON parse error";
    return { ok: false, message };
  }
}

interface MapIssue {
  readonly path: ReadonlyArray<string | number>;
  readonly map: Map<unknown, unknown>;
}

function findFirstMap(
  value: unknown,
  path: ReadonlyArray<string | number> = [],
  seen: WeakSet<object> = new WeakSet(),
): MapIssue | null {
  if (value instanceof Map) {
    return { path, map: value };
  }
  if (value === null || typeof value !== "object") {
    return null;
  }
  if (seen.has(value)) {
    return null;
  }
  seen.add(value);

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const issue = findFirstMap(value[index], [...path, index], seen);
      if (issue) {
        return issue;
      }
    }
    return null;
  }

  const entries = Object.entries(value as Record<string, unknown>);
  for (const [key, entry] of entries) {
    const issue = findFirstMap(entry, [...path, key], seen);
    if (issue) {
      return issue;
    }
  }
  return null;
}

function canonicalizeMapForReport(map: Map<unknown, unknown>, ctx: OracleCtx): unknown {
  const entries = Array.from(map.entries()).map(([key, value]) => {
    const canonicalKey = ctx.canonicalize(key);
    const canonicalValue = ctx.canonicalize(value);
    return {
      key: canonicalKey,
      value: canonicalValue,
      label: JSON.stringify(canonicalKey),
    };
  });
  entries.sort((left, right) => left.label.localeCompare(right.label));
  return entries.map(({ key, value }) => [key, value]);
}

interface CycleIssue {
  readonly path: ReadonlyArray<string | number>;
}

function findFirstCycle(
  value: unknown,
  path: ReadonlyArray<string | number> = [],
  stack: WeakSet<object> = new WeakSet(),
): CycleIssue | null {
  if (value === null || typeof value !== "object") {
    return null;
  }
  if (stack.has(value as object)) {
    return { path };
  }
  stack.add(value as object);

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const issue = findFirstCycle(value[index], [...path, index], stack);
      if (issue) {
        return issue;
      }
    }
    stack.delete(value as object);
    return null;
  }

  if (value instanceof Map) {
    stack.delete(value as object);
    return null;
  }

  const entries = Object.entries(value as Record<string, unknown>);
  for (const [key, entry] of entries) {
    const issue = findFirstCycle(entry, [...path, key], stack);
    if (issue) {
      return issue;
    }
  }
  stack.delete(value as object);
  return null;
}

