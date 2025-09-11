export function saturate(x: unknown, opts: {min: number; max: number}): number {
  if (typeof x !== 'number' || !Number.isInteger(x) || !Number.isInteger(opts.min) || !Number.isInteger(opts.max)) {
    throw new Error('E_L0_TYPE');
  }
  if (opts.min > opts.max) throw new Error('E_L0_BOUNDS');
  if (x < opts.min) return opts.min;
  if (x > opts.max) return opts.max;
  return x;
}
