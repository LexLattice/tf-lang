export function bounds(x: any, opts: any): boolean {
  if (typeof x !== 'number' || !Number.isInteger(x)) {
    throw new Error('x must be integer');
  }
  const min = opts?.min;
  if (min !== undefined && (typeof min !== 'number' || !Number.isInteger(min))) {
    throw new Error('min must be integer');
  }
  const max = opts?.max;
  if (max !== undefined && (typeof max !== 'number' || !Number.isInteger(max))) {
    throw new Error('max must be integer');
  }
  const inclusive = opts?.inclusive !== false;
  if (typeof min === 'number') {
    if (inclusive ? x < min : x <= min) {
      throw new Error(`min bound ${min} violated by ${x}`);
    }
  }
  if (typeof max === 'number') {
    if (inclusive ? x > max : x >= max) {
      throw new Error(`max bound ${max} violated by ${x}`);
    }
  }
  return true;
}
