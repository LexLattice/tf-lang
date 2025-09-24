declare module '*.mjs';

declare module '../../tf-compose/src/parser.mjs' {
  export function parseDSL(source: string): unknown;
}

declare module '../../tf-l0-check/src/check.mjs' {
  export interface CheckVerdict { ok: boolean; reasons?: string[]; }
  export function checkIR(ir: unknown, catalog: unknown, options?: Record<string, unknown>): CheckVerdict;
}

declare module '../../tf-l0-check/src/regions.mjs' {
  export interface RegionVerdict { ok: boolean; reasons: string[]; }
  export function checkRegions(ir: unknown, catalog: unknown, protectedKeywords?: string[]): RegionVerdict;
}

declare module './actions/wrap-authorize.mjs' {
  export interface WrapAuthorizeRange {
    start?: number;
    end?: number;
  }
  export interface WrapAuthorizeResult {
    newText: string;
    start: number;
    end: number;
    before: string;
    after: string;
  }
  export function wrapWithAuthorize(src: string, range?: WrapAuthorizeRange): WrapAuthorizeResult;
}

export {};
