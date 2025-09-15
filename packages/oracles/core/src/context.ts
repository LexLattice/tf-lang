import { canonicalize } from "./canonical.js";
import type { OracleCtx } from "./types.js";

type Canonicalizer = <T>(value: T) => T;

export interface OracleCtxInit {
  readonly seed: string;
  readonly now: number;
  readonly canonicalize?: Canonicalizer;
}

const ensureSeed = (seed: string): string => {
  if (seed.length === 0) {
    throw new Error("oracle seed must not be empty");
  }
  return seed;
};

const ensureNow = (now: number): number => {
  if (!Number.isFinite(now)) {
    throw new Error("oracle context 'now' must be a finite number");
  }
  return now;
};

export const createOracleCtx = (init: OracleCtxInit): OracleCtx => {
  const canonicalizer: Canonicalizer = init.canonicalize ?? canonicalize;
  const ctx: OracleCtx = {
    seed: ensureSeed(init.seed),
    now: ensureNow(init.now),
    canonicalize<T>(value: T): T {
      return canonicalizer(value);
    },
  };
  return Object.freeze(ctx);
};

export const deriveCtx = (base: OracleCtx, overrides: Partial<Omit<OracleCtxInit, "canonicalize">> = {}): OracleCtx =>
  createOracleCtx({
    seed: overrides.seed ?? base.seed,
    now: overrides.now ?? base.now,
    canonicalize: base.canonicalize,
  });

