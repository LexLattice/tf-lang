export function delta_bounded(arr: unknown, bound: unknown): boolean {
  if (!Array.isArray(arr) || typeof bound !== 'number' || !Number.isInteger(bound) || bound < 0) {
    return false;
  }
  for (let i = 1; i < arr.length; i++) {
    const a = arr[i-1];
    const b = arr[i];
    if (typeof a !== 'number' || typeof b !== 'number' || !Number.isInteger(a) || !Number.isInteger(b)) return false;
    if (Math.abs(b - a) > bound) return false;
  }
  return true;
}
