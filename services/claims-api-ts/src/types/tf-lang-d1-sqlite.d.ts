// TEMPORARY AMBIENT TYPES — owner:@you  expires:2025-12-31  replace-with: real sql.js/@tf-lang-d1-sqlite types
declare module "@tf-lang/d1-sqlite" {
  // minimal surface used by claims-api-ts; expand later
  export type D1Database = any;
  export function buildDb(): any;
  export function open(db: D1Database): any;
  const _default: any;
  export default _default;
}
