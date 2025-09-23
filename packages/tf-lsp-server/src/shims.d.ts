declare module '../../tf-compose/src/parser.mjs' {
  export function parseDSL(source: string): unknown;
}

declare module '../../tf-l0-check/src/check.mjs' {
  export interface CheckVerdict {
    ok: boolean;
    reasons?: string[];
  }
  export function checkIR(ir: unknown, catalog: unknown): CheckVerdict;
}

declare module '../../tf-l0-check/src/regions.mjs' {
  export interface RegionVerdict {
    ok: boolean;
    reasons?: string[];
  }
  export function checkRegions(ir: unknown, catalog: unknown, protectedKeywords: string[]): RegionVerdict;
}
