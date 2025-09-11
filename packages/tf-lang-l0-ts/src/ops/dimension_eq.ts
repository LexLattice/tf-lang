export function dimensionEq(a: any, b: any): boolean {
  if (!Array.isArray(a) || !Array.isArray(b)) {
    throw new Error('dimension_eq expects arrays');
  }
  if (a.length !== b.length) {
    throw new Error(`dimension mismatch: ${a.length} vs ${b.length}`);
  }
  return true;
}
