export function bounds(x: unknown, opts: {min?: number; max?: number}): boolean {
  if (typeof x !== 'number' || !Number.isInteger(x)) {
    return false;
  }
  if (opts.min != null && x < opts.min) return false;
  if (opts.max != null && x > opts.max) return false;
  return true;
}
