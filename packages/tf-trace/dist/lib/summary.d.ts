import { TraceRecord } from './validate.js';
export interface TraceSummary {
    total: number;
    by_effect: Record<string, number>;
    by_prim: Record<string, number>;
    ms_total: number;
    ms_by_effect: Record<string, number>;
}
export declare function summarizeTrace(records: TraceRecord[]): TraceSummary;
