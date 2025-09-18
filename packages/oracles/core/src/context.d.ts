import type { Canonicalizer } from "./canonical.js";
import type { OracleCtx } from "./result.js";
export interface OracleCtxInit {
    readonly now?: number;
    readonly canonicalize?: Canonicalizer;
}
export declare function createOracleCtx(seed: string, init?: OracleCtxInit): OracleCtx;
