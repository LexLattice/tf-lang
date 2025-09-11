export function lensMod(x: any, m: any): number {
  if (typeof x !== 'number' || !Number.isInteger(x)) {
    throw new Error('x must be integer');
  }
  if (typeof m !== 'number' || !Number.isInteger(m)) {
    throw new Error('mod must be integer');
  }
  if (m <= 0) throw new Error('mod must be >0');
  const r = ((x % m) + m) % m;
  return r;
}
