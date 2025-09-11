export function lens_mod(x: unknown, m: unknown): number | null {
  if (typeof x !== 'number' || typeof m !== 'number' || !Number.isInteger(x) || !Number.isInteger(m)) {
    return null;
  }
  if (m <= 0) return null;
  const r = ((x % m) + m) % m;
  return r;
}
