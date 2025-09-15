export interface DeterminismCheckpoint {
  readonly label: string;
  readonly state: unknown;
}

export interface DeterminismRun {
  readonly runtime: string;
  readonly checkpoints?: readonly DeterminismCheckpoint[];
  readonly finalState: unknown;
}

export interface DeterminismInput {
  readonly runs: readonly DeterminismRun[];
}

export interface DeterminismReport {
  readonly seed: string;
  readonly runs: readonly {
    readonly runtime: string;
    readonly checkpoints: number;
  }[];
}

export interface DeterminismDiff {
  readonly path: string;
  readonly left: unknown;
  readonly right: unknown;
}
