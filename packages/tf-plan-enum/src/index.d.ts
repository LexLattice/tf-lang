import { PlanGraph, RepoSignals } from '@tf-lang/tf-plan-core';
export interface TfSpecStep {
    readonly op: 'copy' | 'create_vm' | 'create_network';
    readonly params: Record<string, unknown>;
}
export interface TfSpec {
    readonly version: string;
    readonly name: string;
    readonly steps: readonly TfSpecStep[];
}
export interface EnumerateOptions {
    readonly seed?: number;
    readonly beamWidth?: number;
    readonly maxBranches?: number;
    readonly includeChoices?: Readonly<Record<string, readonly string[]>>;
    readonly excludeChoices?: Readonly<Record<string, readonly string[]>>;
    readonly repoSignals?: RepoSignals;
}
export interface EnumeratePlanResult {
    readonly plan: PlanGraph;
    readonly branchCount: number;
}
export declare function readSpec(specPath: string): Promise<TfSpec>;
export declare function enumeratePlan(spec: TfSpec, options?: EnumerateOptions): PlanGraph;
