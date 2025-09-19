import type { Score } from "@tf-lang/tf-plan-core";

export type MetricName = "complexity" | "risk" | "perf" | "devTime" | "depsReady";

export interface ChoiceMetadata {
  readonly keywords?: readonly string[];
  readonly maturity?: number; // 0 (immature) .. 1 (battle tested)
  readonly effort?: number; // 0 (trivial) .. 1 (very complex)
  readonly performance?: number; // 0 (slow) .. 1 (fast)
  readonly risk?: number; // 0 (safe) .. 1 (risky)
  readonly timeToDeliver?: number; // 0 (immediate) .. 1 (long)
  readonly dependencies?: readonly string[];
}

export interface RepoSignals {
  readonly dependencyHealth?: Record<string, number>; // nodeId/dep -> 0..1 readiness
  readonly componentVelocity?: Record<string, number>; // component -> 0..1 (higher faster delivery)
  readonly incidentHistory?: readonly { component: string; severity: number }[];
  readonly adoptionTrend?: Record<string, number>; // choice -> -1..1 sentiment
}

export interface ScoreContext {
  readonly component: string;
  readonly choice: string;
  readonly metadata?: ChoiceMetadata;
  readonly repoSignals?: RepoSignals;
}

export interface MetricResult {
  readonly metric: MetricName;
  readonly value: number;
  readonly weight: number;
  readonly rationale: string;
}

export interface ScoreResult {
  readonly score: Score;
  readonly metrics: readonly MetricResult[];
}
