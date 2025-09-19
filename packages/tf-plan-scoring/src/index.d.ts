import { RepoSignals, Score } from '@tf-lang/tf-plan-core';
type Dimension = 'complexity' | 'risk' | 'perf' | 'devTime' | 'depsReady';
export interface DimensionScore {
    readonly value: number;
    readonly reason: string;
}
export interface ScoreContext {
    readonly component: string;
    readonly choice: string;
    readonly seed: number;
    readonly repoSignals?: RepoSignals;
}
export declare function complexity(component: string, choice: string): DimensionScore;
export declare function risk(component: string, choice: string): DimensionScore;
export declare function perf(component: string, choice: string): DimensionScore;
export declare function devTime(component: string, choice: string): DimensionScore;
export declare function depsReady(component: string, choice: string, repoSignals?: RepoSignals): DimensionScore;
export interface ScorePlanNodeInput extends ScoreContext {
    readonly overrides?: Partial<Record<Dimension, number>>;
}
export declare function scorePlanNode(input: ScorePlanNodeInput): Score;
export {};
