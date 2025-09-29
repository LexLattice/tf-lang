export interface TraceRecord {
    ts: number;
    prim_id: string;
    effect: string;
    ms?: number;
}
export interface ValidationIssue {
    path: string;
    message: string;
}
export type ValidationResult = {
    ok: true;
    record: TraceRecord;
} | {
    ok: false;
    issues: ValidationIssue[];
};
export declare function validateTraceRecord(value: unknown): ValidationResult;
