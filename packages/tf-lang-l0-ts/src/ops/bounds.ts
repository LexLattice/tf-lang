interface BoundsOpts { min?: number; max?: number; inclusive?: boolean }

export function assert_bounds(v: unknown, opts: BoundsOpts): null {
  if (typeof v !== 'number') throw new Error('E_BOUNDS_TYPE');
  if (!Number.isInteger(v)) throw new Error('E_L0_FLOAT');
  const { min = Number.MIN_SAFE_INTEGER, max = Number.MAX_SAFE_INTEGER, inclusive = true } = opts || {};
  if (!Number.isInteger(min) || !Number.isInteger(max)) throw new Error('E_L0_FLOAT');
  if (inclusive) {
    if (v < min || v > max) throw new Error(`E_BOUNDS:${v}`);
  } else {
    if (v <= min || v >= max) throw new Error(`E_BOUNDS:${v}`);
  }
  return null;
}
