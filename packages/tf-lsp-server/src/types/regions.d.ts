export interface RegionVerdict {
  ok: boolean;
  reasons: string[];
}

export function checkRegions(
  ir: unknown,
  catalog: unknown,
  protectedKeywords?: string[]
): RegionVerdict;
