import type { Canonicalizer } from "./canonical.js";
export interface OracleError {
    readonly code: string;
    readonly explain: string;
    readonly details?: unknown;
}
export interface OracleFailure {
    readonly ok: false;
    readonly error: OracleError;
    readonly trace?: readonly string[];
}
export interface OracleSuccess<T> {
    readonly ok: true;
    readonly value: T;
    readonly warnings?: readonly string[];
}
export type OracleResult<T> = OracleSuccess<T> | OracleFailure;
export interface OracleCtx {
    readonly seed: string;
    readonly now: number;
    readonly canonicalize: Canonicalizer;
}
export type Oracle<I, O> = {
    check(input: I, ctx: OracleCtx): Promise<OracleResult<O>> | OracleResult<O>;
};
export declare function ok<T>(value: T, warnings?: Iterable<string>): OracleSuccess<T>;
export declare function err(code: string, explain: string, details?: unknown): OracleFailure;
export declare function withTrace(base: OracleFailure, trace: Iterable<string>): OracleFailure;
