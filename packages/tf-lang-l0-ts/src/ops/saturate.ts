interface SatOpts { min: number; max: number }

export function saturate(v: unknown, opts: SatOpts): number {
  if (typeof v !== 'number') throw new Error('E_SAT_TYPE');
  if (!Number.isInteger(v) || !Number.isInteger(opts.min) || !Number.isInteger(opts.max)) {
    throw new Error('E_L0_FLOAT');
  }
  const min = opts.min;
  const max = opts.max;
  if (min > max) throw new Error('E_SAT_BOUNDS');
  if (v < min) return min;
  if (v > max) return max;
  return v;
}
