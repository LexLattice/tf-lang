export interface DeterminismRun {
  readonly runId: string;
  readonly final: unknown;
  readonly checkpoints?: Readonly<Record<string, unknown>>;
  readonly note?: string;
}

export interface DeterminismCase {
  readonly name: string;
  readonly seed: string;
  readonly runs: ReadonlyArray<DeterminismRun>;
}

export interface DeterminismInput {
  readonly cases: ReadonlyArray<DeterminismCase>;
}

export interface DeterminismReport {
  readonly casesChecked: number;
  readonly runsChecked: number;
}

export interface CheckpointMismatch {
  readonly checkpoint: string;
  readonly expected: unknown;
  readonly actual: unknown;
}

export interface CaseMismatch {
  readonly case: string;
  readonly seed: string;
  readonly run: string;
  readonly mismatches: ReadonlyArray<CheckpointMismatch>;
}

export interface CanonicalRun {
  readonly runId: string;
  readonly final: unknown;
  readonly checkpoints: Record<string, unknown>;
}
