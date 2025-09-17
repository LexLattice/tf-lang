import { canonicalJson, err, ok, withTrace } from "@tf/oracles-core";
import type { Oracle, OracleCtx, OracleResult } from "@tf/oracles-core";

import type {
  CaseMismatch,
  CanonicalRun,
  CheckpointMismatch,
  DeterminismInput,
  DeterminismReport,
  DeterminismRun,
} from "./types.js";

export type { DeterminismCase, DeterminismInput, DeterminismReport, DeterminismRun } from "./types.js";

const FAILURE_CODE = "E_NON_DETERMINISTIC";

export function createDeterminismOracle(): Oracle<DeterminismInput, DeterminismReport> {
  return {
    async check(input, ctx) {
      return checkDeterminism(input, ctx);
    },
  };
}

export async function checkDeterminism(
  input: DeterminismInput,
  ctx: OracleCtx,
): Promise<OracleResult<DeterminismReport>> {
  const cases = input.cases ?? [];
  let casesChecked = 0;
  let runsChecked = 0;
  const mismatches: CaseMismatch[] = [];

  for (const determinismCase of cases) {
    casesChecked += 1;
    const canonicalRuns = determinismCase.runs.map((run) => canonicalizeRun(run, ctx));
    runsChecked += canonicalRuns.length;

    if (canonicalRuns.length <= 1) {
      continue;
    }

    const baseline = canonicalRuns[0];
    for (let index = 1; index < canonicalRuns.length; index += 1) {
      const candidate = canonicalRuns[index];
      const runMismatches = diffRuns(baseline, candidate);
      if (runMismatches.length > 0) {
        mismatches.push({
          case: determinismCase.name,
          seed: determinismCase.seed,
          run: candidate.runId,
          mismatches: runMismatches,
        });
      }
    }
  }

  if (mismatches.length > 0) {
    const trace = mismatches
      .slice(0, 5)
      .map((item) => `case:${item.case}:run:${item.run}`);
    const failure = err(FAILURE_CODE, "Runs diverged under identical seeds", {
      mismatches,
    });
    return withTrace(failure, trace);
  }

  return ok({ casesChecked, runsChecked });
}

function canonicalizeRun(run: DeterminismRun, ctx: OracleCtx): CanonicalRun {
  const checkpoints = run.checkpoints ?? {};
  const canonicalCheckpoints: Record<string, unknown> = {};
  for (const [name, value] of Object.entries(checkpoints)) {
    canonicalCheckpoints[name] = ctx.canonicalize(value);
  }
  return {
    runId: run.runId,
    final: ctx.canonicalize(run.final),
    checkpoints: canonicalCheckpoints,
  };
}

function diffRuns(baseline: CanonicalRun, candidate: CanonicalRun): CheckpointMismatch[] {
  const mismatches: CheckpointMismatch[] = [];
  if (!sameValue(baseline.final, candidate.final)) {
    mismatches.push({ checkpoint: "final", expected: baseline.final, actual: candidate.final });
  }

  const allKeys = new Set([
    ...Object.keys(baseline.checkpoints),
    ...Object.keys(candidate.checkpoints),
  ]);
  for (const key of Array.from(allKeys).sort()) {
    const expected = key in baseline.checkpoints ? baseline.checkpoints[key] : undefined;
    const actual = key in candidate.checkpoints ? candidate.checkpoints[key] : undefined;
    if (!sameValue(expected, actual)) {
      mismatches.push({ checkpoint: key, expected, actual });
    }
  }

  return mismatches;
}

function sameValue(left: unknown, right: unknown): boolean {
  return canonicalJson(left) === canonicalJson(right);
}
