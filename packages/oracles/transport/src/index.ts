import { canonicalStringify, diffValues, err, ok, withTrace } from "@tf/oracles-core";
import type { Oracle, OracleCtx, OracleResult } from "@tf/oracles-core";

import type { TransportCase, TransportDrift, TransportInput, TransportReport } from "./types.js";

export type { TransportCase, TransportDrift, TransportInput, TransportReport } from "./types.js";

const FAILURE_CODE = "E_TRANSPORT_DRIFT" as const;
const PARSE_FAILURE_CODE = "E_TRANSPORT_DECODE" as const;
const MISSING_VALUE = "[missing]" as const;

interface NormalizedCase {
  readonly name?: string;
  readonly seed?: string;
  readonly json: string;
  readonly value: unknown;
}

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
  const drifts: TransportDrift[] = [];
  let casesChecked = 0;
  let sawParseFailure = false;

  for (const entry of cases) {
    casesChecked += 1;
    const parsed = safeParse(entry.json);
    if (!parsed.ok) {
      drifts.push({
        case: entry.name,
        seed: entry.seed,
        pointer: "",
        expected: "[valid json]",
        actual: parsed.error,
      });
      sawParseFailure = true;
      continue;
    }

    const canonicalDecoded = ctx.canonicalize(parsed.value ?? null);
    const canonicalRuntime = ctx.canonicalize(entry.value ?? null);

    const encodedDecoded = canonicalStringify(canonicalDecoded);
    const encodedRuntime = canonicalStringify(canonicalRuntime);

    if (encodedDecoded !== encodedRuntime) {
      const diff = diffValues(canonicalDecoded, canonicalRuntime, { missingValue: MISSING_VALUE });
      if (diff) {
        drifts.push({
          case: entry.name,
          seed: entry.seed,
          pointer: diff.pointer,
          expected: diff.left,
          actual: diff.right,
        });
      } else {
        drifts.push({
          case: entry.name,
          seed: entry.seed,
          pointer: "",
          expected: canonicalDecoded,
          actual: canonicalRuntime,
        });
      }
    }
  }

  if (drifts.length > 0) {
    const trace = drifts.slice(0, 5).map((drift) => {
      const label = drift.case ?? "unknown";
      return drift.seed ? `${label}:seed:${drift.seed}` : label;
    });
    const failure = err(sawParseFailure ? PARSE_FAILURE_CODE : FAILURE_CODE, "Transport round-trip drifted", { drifts });
    return withTrace(failure, trace);
  }

  return ok({ casesChecked });
}

function normalizeCases(input: TransportInput): NormalizedCase[] {
  const result: NormalizedCase[] = [];
  const candidates: TransportCase[] = [];

  if (Array.isArray(input.cases)) {
    for (const entry of input.cases) {
      if (entry && typeof entry === "object") {
        candidates.push(entry);
      }
    }
  }

  if (typeof input.json === "string") {
    candidates.push({ json: input.json, value: input.value });
  }

  for (const candidate of candidates) {
    if (!candidate) {
      continue;
    }
    const json = typeof candidate.json === "string" ? candidate.json : undefined;
    if (!json) {
      continue;
    }
    const value = Object.prototype.hasOwnProperty.call(candidate, "value") ? candidate.value : null;
    result.push({
      name: candidate.name,
      seed: candidate.seed,
      json,
      value,
    });
  }

  return result;
}

function safeParse(json: string): { ok: true; value: unknown } | { ok: false; error: string } {
  try {
    return { ok: true, value: JSON.parse(json) };
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    return { ok: false, error: message };
  }
}
