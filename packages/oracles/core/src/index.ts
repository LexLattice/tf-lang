export type {
  Oracle,
  OracleCheck,
  OracleCtx,
  OracleError,
  OracleFailure,
  OracleOk,
  OracleResult,
} from "./types.js";

export { defineOracle } from "./oracle.js";
export { createOracleCtx, deriveCtx } from "./context.js";
export {
  canonicalize,
  canonicalStringify,
  canonicalBuffer,
} from "./canonical.js";
export {
  ok,
  mergeWarnings,
  error,
  failure,
  fromError,
  isOk,
  mapValue,
  formatFailure,
} from "./result.js";

