import type { OracleCtx } from "./context.js";
import type { OracleOutcome } from "./result.js";

export type Oracle<I, O> = (
  input: I,
  ctx: OracleCtx
) => OracleOutcome<O> | Promise<OracleOutcome<O>>;
