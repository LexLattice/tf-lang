export declare const PLAN_GRAPH_VERSION = "0.1.0";
export interface Score {
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
    readonly score: Score;
}
export interface PlanEdge {
    readonly from: string;
    readonly to: string;
    readonly kind: 'depends' | 'sequence';
}
export interface PlanGraphMeta {
    readonly seed: number;
    readonly specHash: string;
    readonly version: string;
}
export interface PlanGraph {
    readonly version: string;
    readonly nodes: readonly PlanNode[];
    readonly edges: readonly PlanEdge[];
    readonly meta: PlanGraphMeta;
}
export interface StableIdInput {
    readonly scope: string;
    readonly specId: string;
    readonly component: string;
    readonly choice: string;
    readonly seed: number;
    readonly version: string;
}
export interface StableIdResult {
    readonly full: string;
    readonly short: string;
}
export declare function stableId(input: StableIdInput): StableIdResult;
export declare function deepFreeze<T>(value: T): Readonly<T>;
export type Comparator<T> = (a: T, b: T) => number;
export declare function stableSort<T>(items: readonly T[], compare: Comparator<T>): T[];
export interface SeededRng {
    next(): number;
    nextInt(maxExclusive: number): number;
}
export declare function seedRng(seed: number | string): SeededRng;
export declare function canonicalStringify(value: unknown): string;
export declare function hashObject(value: unknown): string;
export type RepoSignals = Readonly<Record<string, unknown>>;
export declare const planSchema: Readonly<Record<string, unknown>>;
export declare const branchSchema: Readonly<Record<string, unknown>>;
export declare const compareSchema: Readonly<Record<string, unknown>>;
export declare function validateBranch(node: PlanNode, context?: string): PlanNode;
export declare function validatePlan(plan: PlanGraph, context?: string): PlanGraph;
export declare function validateCompare<T>(report: T, context?: string): T;
