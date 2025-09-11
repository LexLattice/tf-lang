export function deltaBounded(seq: any, bound: any): boolean {
  if (!Array.isArray(seq)) throw new Error('delta_bounded expects array');
  if (typeof bound !== 'number' || !Number.isInteger(bound) || bound < 0) {
    throw new Error('bound must be non-negative integer');
  }
  for (let i = 1; i < seq.length; i++) {
    const prev = seq[i - 1];
    const cur = seq[i];
    if (!Number.isInteger(prev) || !Number.isInteger(cur)) {
      throw new Error('seq must contain integers');
    }
    const diff = cur - prev;
    if (Math.abs(diff) > bound) {
      return { index: i, delta: diff };
    }
  }
  return true;
}
