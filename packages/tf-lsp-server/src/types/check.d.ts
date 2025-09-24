export interface CheckVerdict {
  ok: boolean;
  reasons?: string[];
}

export function checkIR(
  ir: unknown,
  catalog: unknown,
  options?: Record<string, unknown>
): CheckVerdict;
