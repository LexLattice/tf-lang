export function delta_bounded(seq: unknown, bound: unknown): null {
  if (!Array.isArray(seq) || typeof bound !== 'number') {
    throw new Error('E_DELTA_TYPE');
  }
  if (!Number.isInteger(bound)) throw new Error('E_L0_FLOAT');
  if (bound < 0) throw new Error('E_DELTA_BOUNDS');
  let prev: number | undefined;
  for (let i = 0; i < seq.length; i++) {
    const v = seq[i];
    if (typeof v !== 'number' || !Number.isInteger(v)) {
      throw new Error('E_L0_FLOAT');
    }
    if (prev !== undefined) {
      const d = Math.abs(v - prev);
      if (d > bound) {
        throw new Error(`E_DELTA_BOUNDS:${i}:${d}`);
      }
    }
    prev = v;
  }
  return null;
}
