export function saturate(x: any, min: any, max: any, field = '') {
  if (typeof x !== 'number' || !Number.isInteger(x)) {
    throw new Error('x must be integer');
  }
  if (typeof min !== 'number' || !Number.isInteger(min)) {
    throw new Error('min must be integer');
  }
  if (typeof max !== 'number' || !Number.isInteger(max)) {
    throw new Error('max must be integer');
  }
  if (min > max) throw new Error('min > max');
  let v = x;
  if (v < min) v = min;
  if (v > max) v = max;
  const journal = v === x ? null : { field, before: x, after: v, reason: 'saturate' };
  return { tag: 'sat', values: [v, journal] };
}
