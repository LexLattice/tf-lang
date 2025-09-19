export type MetricName = "complexity" | "risk" | "perf" | "devTime" | "depsReady";

export interface ChoiceMetadata {
  readonly description?: string;
  readonly tags?: readonly string[];
  readonly heuristics?: Partial<Record<MetricName, number>>;
}

export interface ComponentSignals {
  readonly stability?: number;
  readonly performance?: number;
  readonly velocity?: number;
  readonly readiness?: number;
  readonly incidents?: number;
}

export interface RepoSignals {
  readonly componentSignals?: Record<string, ComponentSignals>;
  readonly global?: {
    readonly adoption?: number;
    readonly riskFloor?: number;
  };
}

export interface ScoreContext {
  readonly component: string;
  readonly choice: string;
  readonly metadata?: ChoiceMetadata;
  readonly repoSignals?: RepoSignals;
}

export interface ScoreDetail {
  readonly value: number;
  readonly explanation: string;
}
