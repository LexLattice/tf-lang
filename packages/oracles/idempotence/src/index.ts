import { diffCanonical, err, ok, withTrace } from "@tf/oracles-core";
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
      const diff = diffCanonical(baseline.value, candidate.value, { missingValue: MISSING_VALUE });
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

