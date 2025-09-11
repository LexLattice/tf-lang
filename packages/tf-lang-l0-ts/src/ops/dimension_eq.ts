export function dimension_eq(a: unknown, b: unknown): null {
  if (!Array.isArray(a) || !Array.isArray(b)) {
    throw new Error('E_DIMENSION_TYPE');
  }
  if (a.length !== b.length) {
    throw new Error('E_DIMENSION_MISMATCH');
  }
  return null;
}
