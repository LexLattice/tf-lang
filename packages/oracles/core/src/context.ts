import type { Canonicalizer } from "./canonical.js";
import { defaultCanonicalize } from "./canonical.js";
import type { OracleCtx } from "./result.js";

export interface OracleCtxInit {
  readonly now?: number;
  readonly canonicalize?: Canonicalizer;
}

export function createOracleCtx(seed: string, init: OracleCtxInit = {}): OracleCtx {
  return {
    seed,
    now: init.now ?? 0,
    canonicalize: init.canonicalize ?? defaultCanonicalize,
  };
}
