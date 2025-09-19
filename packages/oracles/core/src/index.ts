export type { Canonicalizer } from "./canonical.js";
export { canonicalStringify, defaultCanonicalize } from "./canonical.js";
export type { DiffOptions, DiffResult } from "./diff.js";
export {
  diffValues,
  escapePointerSegment,
  isPlainObject,
  pointerFromSegments,
} from "./diff.js";
export type {
  Oracle,
  OracleCtx,
  OracleError,
  OracleFailure,
  OracleResult,
  OracleSuccess,
} from "./result.js";
export { err, ok, withTrace } from "./result.js";
export type { OracleCtxInit } from "./context.js";
export { createOracleCtx } from "./context.js";
