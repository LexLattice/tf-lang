import type { ComponentSignals, MetricName, RepoSignals } from "@tf-lang/tf-plan-scoring";

export interface TfPlanDesignChoice {
  readonly id: string;
  readonly title?: string;
  readonly summary?: string;
  readonly rationale?: string;
  readonly tags?: readonly string[];
  readonly heuristics?: Partial<Record<MetricName, number>>;
  readonly dependsOn?: readonly string[];
  readonly excludes?: readonly string[];
  readonly requires?: readonly string[];
  readonly provides?: readonly string[];
  readonly signals?: ComponentSignals;
}

export interface TfPlanComponent {
  readonly component: string;
  readonly description?: string;
  readonly choices: readonly TfPlanDesignChoice[];
}

export interface TfPlanSpec {
  readonly version: string;
  readonly name: string;
  readonly designSpace: readonly TfPlanComponent[];
  readonly repoSignals?: RepoSignals;
}

export interface EnumerateConstraints {
  readonly include?: Record<string, readonly string[]>;
  readonly exclude?: Record<string, readonly string[]>;
  readonly requires?: readonly string[];
}

export interface EnumerateOptions {
  readonly seed?: number;
  readonly beamWidth?: number;
  readonly maxNodes?: number;
  readonly constraints?: EnumerateConstraints;
}

export interface EnumeratedPlanNode {
  readonly nodeId: string;
  readonly choice: TfPlanDesignChoice;
  readonly component: TfPlanComponent;
}
