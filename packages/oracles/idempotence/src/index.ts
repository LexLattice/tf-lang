import { err, ok, withTrace } from "@tf/oracles-core";
import type { Oracle, OracleCtx, OracleResult } from "@tf/oracles-core";

import { diffCanonical } from "./diff.js";
import type {
  IdempotenceCase,
  IdempotenceInput,
  IdempotenceMismatch,
  IdempotenceReport,
  IdempotenceViolation,
} from "./types.js";

export type {
  IdempotenceCase,
  IdempotenceInput,
  IdempotenceMismatch,
  IdempotenceReport,
  IdempotenceViolation,
} from "./types.js";

const FAILURE_CODE = "E_NOT_IDEMPOTENT";

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
  const cases = [...(input.cases ?? [])];
  let passed = 0;
  const violations: IdempotenceViolation[] = [];

  for (let index = 0; index < cases.length; index += 1) {
    const idempotenceCase = cases[index];
    const mismatch = evaluateCase(idempotenceCase, ctx);
    if (mismatch) {
      violations.push({
        caseName: idempotenceCase.name,
        seed: ctx.seed,
        mismatch: decoratePointer(mismatch, index),
      });
      continue;
    }
    passed += 1;
  }

  const report: IdempotenceReport = {
    total: cases.length,
    passed,
    failed: cases.length - passed,
    ...(violations.length > 0 ? { firstFail: violations[0].mismatch } : {}),
  };

  if (violations.length === 0) {
    return ok(report);
  }

  const trace = violations.slice(0, 5).map((item) => `case:${item.caseName}`);
  const failure = err(FAILURE_CODE, "operation was not idempotent", {
    report,
    violations,
  });
  return withTrace(failure, trace);
}

function evaluateCase(
  idempotenceCase: IdempotenceCase,
  ctx: OracleCtx,
): IdempotenceMismatch | undefined {
  const once = ctx.canonicalize(idempotenceCase.once);
  const twice = ctx.canonicalize(idempotenceCase.twice);
  return diffCanonical(once, twice);
}

function decoratePointer(
  mismatch: IdempotenceMismatch,
  index: number,
): IdempotenceMismatch {
  const base = `/cases/${escapeSegment(String(index))}`;
  if (mismatch.pointer === "/") {
    return { ...mismatch, pointer: base };
  }
  return { ...mismatch, pointer: `${base}${mismatch.pointer}` };
}

function escapeSegment(segment: string): string {
  return segment.replace(/~/g, "~0").replace(/\//g, "~1");
}
