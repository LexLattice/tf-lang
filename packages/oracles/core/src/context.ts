import { canonicalize } from "./canonical.js";

export interface OracleCtx {
  readonly seed: string;
  readonly now: number;
  readonly canonicalize: (value: unknown) => unknown;
}

export function createCtx(seed: string, now: number): OracleCtx {
  return {
    seed,
    now,
    canonicalize,
  };
}
