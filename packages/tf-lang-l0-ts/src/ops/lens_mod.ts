export function lens_mod(x: unknown, m: unknown): number {
  if (typeof x !== 'number' || typeof m !== 'number') {
    throw new Error('E_MOD_TYPE');
  }
  if (!Number.isInteger(x) || !Number.isInteger(m)) {
    throw new Error('E_L0_FLOAT');
  }
  if (m <= 0) {
    throw new Error('E_MOD_BOUNDS');
  }
  const r = ((x % m) + m) % m;
  return r;
}
