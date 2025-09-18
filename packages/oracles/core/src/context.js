import { defaultCanonicalize } from "./canonical.js";
export function createOracleCtx(seed, init = {}) {
    return {
        seed,
        now: init.now ?? 0,
        canonicalize: init.canonicalize ?? defaultCanonicalize,
    };
}
