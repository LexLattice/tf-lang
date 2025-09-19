export interface ScoreBreakdown {
  readonly metric: string;
  readonly value: number;
  readonly weight?: number;
  readonly rationale: string;
}

export interface Score {
  readonly total: number;
  readonly complexity: number;
  readonly risk: number;
  readonly perf: number;
  readonly devTime: number;
  readonly depsReady: number;
  readonly explain: readonly ScoreBreakdown[];
}

export interface PlanNode {
  readonly nodeId: string;
  readonly specId: string;
  readonly component: string;
  readonly choice: string;
  readonly deps: readonly string[];
  readonly rationale: string;
  readonly score: Score;
}

export type PlanEdgeKind = "dependency" | "conflict" | "composes";

export interface PlanEdge {
  readonly from: string;
  readonly to: string;
  readonly kind: PlanEdgeKind;
}

export interface PlanMeta {
  readonly seed: number;
  readonly specHash: string;
  readonly version: string;
  readonly generatedAt: string;
}

export interface PlanGraph {
  readonly nodes: readonly PlanNode[];
  readonly edges: readonly PlanEdge[];
  readonly meta: PlanMeta;
}

export interface BranchSummary {
  readonly node: PlanNode;
  readonly position: number;
}

export const PLAN_SCHEMA_VERSION = "1.0.0" as const;
