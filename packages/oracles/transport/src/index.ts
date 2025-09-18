import { diffCanonical, err, ok, withTrace } from "@tf/oracles-core";
import type { Oracle, OracleCtx, OracleResult } from "@tf/oracles-core";

import type { TransportInput, TransportMismatch, TransportReport } from "./types.js";

export type { TransportInput, TransportMismatch, TransportReport } from "./types.js";

const FAILURE_CODE = "E_TRANSPORT_DIVERGED" as const;
const SERIALIZATION_CODE = "E_TRANSPORT_SERIALIZE" as const;
const PARSE_CODE = "E_TRANSPORT_PARSE" as const;
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
  const baseline = ctx.canonicalize(input.value);

  let encoded: string | undefined;
  try {
    encoded = JSON.stringify(input.value);
  } catch (error) {
    return err(SERIALIZATION_CODE, "Value is not JSON serializable", {
      reason: describeError(error),
    });
  }

  if (encoded === undefined) {
    return err(SERIALIZATION_CODE, "Value is not JSON serializable", {
      reason: "JSON.stringify returned undefined",
    });
  }

  let decoded: unknown;
  try {
    decoded = JSON.parse(encoded);
  } catch (error) {
    const failure = err(PARSE_CODE, "Serialized payload could not be parsed", {
      reason: describeError(error),
      encoded,
    });
    return withTrace(failure, ["parse"]);
  }

  const roundTrip = ctx.canonicalize(decoded);
  const diff = diffCanonical(baseline, roundTrip, { missingValue: MISSING_VALUE });
  if (diff) {
    const mismatch: TransportMismatch = {
      pointer: diff.pointer,
      expected: diff.left,
      actual: diff.right,
    };
    const failure = err(FAILURE_CODE, "JSON round-trip diverged", {
      mismatches: [mismatch],
      encoded,
    });
    return withTrace(failure, [`pointer:${mismatch.pointer}`]);
  }

  return ok({ encoded });
}

function describeError(error: unknown): string {
  if (error instanceof Error) {
    const name = error.name?.trim();
    const message = error.message?.trim();
    if (name && message) {
      return `${name}: ${message}`;
    }
    if (message) {
      return message;
    }
    if (name) {
      return name;
    }
    return "Error";
  }
  if (typeof error === "string") {
    return error;
  }
  try {
    return JSON.stringify(error);
  } catch {
    return String(error);
  }
}
