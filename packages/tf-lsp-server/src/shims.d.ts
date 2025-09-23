declare module 'tf-compose/parser' {
  export function parseDSL(source: string): unknown;
}

declare module 'tf-l0/check' {
  export interface CheckVerdict {
    ok: boolean;
    reasons?: string[];
  }

  export function checkIR(
    ir: unknown,
    catalog: unknown,
    options?: Record<string, unknown>
  ): CheckVerdict;
}

declare module 'tf-l0/regions' {
  export interface RegionVerdict {
    ok: boolean;
    reasons: string[];
  }

  export function checkRegions(
    ir: unknown,
    catalog: unknown,
    protectedList?: string[]
  ): RegionVerdict;
}
