export const PLAN_GRAPH_VERSION = "0.1.0" as const;

export interface ScoreBreakdown {
  readonly total: number;
  readonly complexity: number;
  readonly risk: number;
  readonly perf: number;
  readonly devTime: number;
  readonly depsReady: number;
  readonly explain: readonly string[];
}

export interface PlanNode {
  readonly nodeId: string;
  readonly specId: string;
  readonly component: string;
  readonly choice: string;
  readonly deps: readonly string[];
  readonly rationale: string;
  readonly score: ScoreBreakdown;
}

export type PlanEdgeKind = "depends_on" | "composes";

export interface PlanEdge {
  readonly from: string;
  readonly to: string;
  readonly kind: PlanEdgeKind;
}

export interface PlanGraphMeta {
  readonly seed: number;
  readonly specHash: string;
  readonly specId: string;
  readonly version: string;
}

export interface PlanGraph {
  readonly nodes: readonly PlanNode[];
  readonly edges: readonly PlanEdge[];
  readonly meta: PlanGraphMeta;
}

export interface StableIdInput {
  readonly scope: string;
  readonly specId: string;
  readonly component: string;
  readonly choice: string;
  readonly seed: number | string;
  readonly version: string;
}

export interface SeededRng {
  next(): number;
  integer(maxExclusive: number): number;
}

export interface ScoreAggregateOptions {
  readonly weights?: Partial<{
    complexity: number;
    risk: number;
    perf: number;
    devTime: number;
    depsReady: number;
  }>;
}
