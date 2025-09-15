import { err, ok, type Oracle } from "@tf/oracles-core";
import type {
  DeterminismCheckpoint,
  DeterminismDiff,
  DeterminismInput,
  DeterminismReport,
  DeterminismRun,
} from "./types.js";

const ERROR_CODES = {
  insufficientRuns: "E_DETERMINISM_INSUFFICIENT_RUNS",
  checkpointCount: "E_DETERMINISM_CHECKPOINT_COUNT",
  checkpointLabel: "E_DETERMINISM_CHECKPOINT_LABEL",
  checkpointState: "E_DETERMINISM_CHECKPOINT_STATE",
  finalState: "E_DETERMINISM_FINAL_STATE",
} as const;

const MISSING = Object.freeze({ missing: true });

function normalizeRun(run: DeterminismRun): {
  runtime: string;
  checkpoints: DeterminismCheckpoint[];
  finalState: unknown;
} {
  return {
    runtime: run.runtime,
    checkpoints: Array.from(run.checkpoints ?? []).map((cp) => ({
      label: cp.label,
      state: cp.state,
    })),
    finalState: run.finalState,
  };
}

function encodeToken(token: string): string {
  return token.replace(/~/g, "~0").replace(/\//g, "~1");
}

function joinPath(base: string, token: string): string {
  const encoded = encodeToken(token);
  return base === "" ? `/${encoded}` : `${base}/${encoded}`;
}

function isPlainRecord(value: unknown): value is Record<string, unknown> {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function diffCanonical(
  baseline: unknown,
  candidate: unknown,
  path = ""
): DeterminismDiff | null {
  if (Object.is(baseline, candidate)) {
    return null;
  }

  if (Array.isArray(baseline) && Array.isArray(candidate)) {
    const maxLength = Math.max(baseline.length, candidate.length);
    for (let idx = 0; idx < maxLength; idx += 1) {
      if (idx >= baseline.length) {
        return {
          path: joinPath(path, String(idx)),
          left: MISSING,
          right: candidate[idx] ?? MISSING,
        };
      }
      if (idx >= candidate.length) {
        return {
          path: joinPath(path, String(idx)),
          left: baseline[idx] ?? MISSING,
          right: MISSING,
        };
      }
      const diff = diffCanonical(
        baseline[idx],
        candidate[idx],
        joinPath(path, String(idx))
      );
      if (diff) {
        return diff;
      }
    }
    return null;
  }

  if (isPlainRecord(baseline) && isPlainRecord(candidate)) {
    const keys = new Set([
      ...Object.keys(baseline as Record<string, unknown>),
      ...Object.keys(candidate as Record<string, unknown>),
    ]);
    const ordered = Array.from(keys).sort();
    for (const key of ordered) {
      if (!(key in baseline)) {
        return {
          path: joinPath(path, key),
          left: MISSING,
          right: (candidate as Record<string, unknown>)[key],
        };
      }
      if (!(key in candidate)) {
        return {
          path: joinPath(path, key),
          left: (baseline as Record<string, unknown>)[key],
          right: MISSING,
        };
      }
      const diff = diffCanonical(
        (baseline as Record<string, unknown>)[key],
        (candidate as Record<string, unknown>)[key],
        joinPath(path, key)
      );
      if (diff) {
        return diff;
      }
    }
    return null;
  }

  return {
    path: path === "" ? "/" : path,
    left: baseline,
    right: candidate,
  };
}

function canonicalEquals(a: unknown, b: unknown): boolean {
  return JSON.stringify(a) === JSON.stringify(b);
}

export const determinismOracle: Oracle<DeterminismInput, DeterminismReport> = (
  input,
  ctx
) => {
  if (!input.runs || input.runs.length < 2) {
    return err(ERROR_CODES.insufficientRuns, "need at least two runs to compare", {
      details: ctx.canonicalize({ runCount: input.runs?.length ?? 0 }),
    });
  }

  const runs = input.runs.map(normalizeRun);
  const baseline = runs[0];
  const baselineCheckpoints = baseline.checkpoints;
  const baselineCanonicalCheckpoints = baselineCheckpoints.map((cp) => ({
    label: cp.label,
    state: ctx.canonicalize(cp.state),
  }));
  const baselineFinal = ctx.canonicalize(baseline.finalState);

  for (let i = 1; i < runs.length; i += 1) {
    const candidate = runs[i];
    const trace = [baseline.runtime, candidate.runtime] as const;
    const candidateCheckpoints = candidate.checkpoints;
    if (baselineCheckpoints.length !== candidateCheckpoints.length) {
      return err(
        ERROR_CODES.checkpointCount,
        "checkpoint count mismatch",
        {
          details: ctx.canonicalize({
            baseline: baselineCheckpoints.length,
            candidate: candidateCheckpoints.length,
            runtimes: { baseline: baseline.runtime, candidate: candidate.runtime },
          }),
          trace,
        }
      );
    }

    for (let idx = 0; idx < baselineCheckpoints.length; idx += 1) {
      const baseCp = baselineCheckpoints[idx];
      const candCp = candidateCheckpoints[idx];
      if (baseCp.label !== candCp.label) {
        return err(ERROR_CODES.checkpointLabel, "checkpoint labels diverged", {
          details: ctx.canonicalize({
            index: idx,
            baseline: baseCp.label,
            candidate: candCp.label,
          }),
          trace,
        });
      }
      const candidateCanonical = ctx.canonicalize(candCp.state);
      const referenceCanonical = baselineCanonicalCheckpoints[idx].state;
      if (!canonicalEquals(referenceCanonical, candidateCanonical)) {
        const diff = diffCanonical(referenceCanonical, candidateCanonical);
        return err(ERROR_CODES.checkpointState, "checkpoint states diverged", {
          details: ctx.canonicalize({
            index: idx,
            label: baseCp.label,
            diff,
          }),
          trace,
        });
      }
    }

    const candidateFinal = ctx.canonicalize(candidate.finalState);
    if (!canonicalEquals(baselineFinal, candidateFinal)) {
      const diff = diffCanonical(baselineFinal, candidateFinal);
      return err(ERROR_CODES.finalState, "final state diverged", {
        details: ctx.canonicalize({ diff }),
        trace,
      });
    }
  }

  const report: DeterminismReport = {
    seed: ctx.seed,
    runs: runs.map((run) => ({
      runtime: run.runtime,
      checkpoints: run.checkpoints.length,
    })),
  };
  return ok(report);
};
