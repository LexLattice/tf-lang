import { TraceRecord, ValidationIssue } from './validate.js';
export interface TraceIngestError {
    line: number;
    message: string;
    issues?: ValidationIssue[];
    raw?: string;
}
export interface TraceIngestResult {
    records: TraceRecord[];
    errors: TraceIngestError[];
}
export declare function ingestTraceFile(path: string): Promise<TraceIngestResult>;
