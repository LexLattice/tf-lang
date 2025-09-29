import { TraceSummary } from './summary.js';
export interface EffectBudget {
    ms_max?: number;
    count_max?: number;
}
export interface TraceBudgetSpec {
    total_ms_max?: number;
    by_effect?: Record<string, EffectBudget>;
}
export interface BudgetResult {
    ok: boolean;
    reasons: string[];
}
export declare function evaluateBudget(summary: TraceSummary, spec: TraceBudgetSpec): BudgetResult;
