import { TfRegistry, Value } from '../model/types.js';

function expectInt(n: any) {
  if (typeof n !== 'number' || !Number.isInteger(n)) {
    throw new Error('E_L0_FLOAT');
  }
}

export function assertDimensionEq([a, b]: Value[]): boolean {
  if (!Array.isArray(a) || !Array.isArray(b)) throw new Error('E_TYPE');
  expectInt(a.length);
  expectInt(b.length);
  if (a.length !== b.length) throw new Error(`dimension mismatch: ${a.length} != ${b.length}`);
  return true;
}

export function lensMod([x, m]: Value[]): number {
  expectInt(x);
  expectInt(m);
  if (m <= 0) throw new Error('E_MOD_BOUNDS');
  let r = x % m;
  if (r < 0) r += m;
  return r;
}

export function assertBounds([x, opts]: Value[]): boolean {
  expectInt(x);
  const { min, max, inclusive = true } = opts || {};
  if (min !== undefined) {
    expectInt(min);
    if (inclusive ? x < min : x <= min) throw new Error(`bounds: ${x} < ${min}`);
  }
  if (max !== undefined) {
    expectInt(max);
    if (inclusive ? x > max : x >= max) throw new Error(`bounds: ${x} > ${max}`);
  }
  return true;
}

export function probeDeltaBounded([seq, bound]: Value[]): boolean {
  if (!Array.isArray(seq)) throw new Error('E_TYPE');
  expectInt(bound);
  for (let i = 1; i < seq.length; i++) {
    const a = seq[i - 1];
    const b = seq[i];
    expectInt(a);
    expectInt(b);
    const d = Math.abs(a - b);
    if (d > bound) throw new Error(`delta ${d} at index ${i}`);
  }
  return true;
}

export function correctSaturate([x, opts]: Value[]): number {
  expectInt(x);
  let v = x;
  if (opts && opts.min !== undefined) { expectInt(opts.min); if (v < opts.min) v = opts.min; }
  if (opts && opts.max !== undefined) { expectInt(opts.max); if (v > opts.max) v = opts.max; }
  return v;
}

export const registry = new TfRegistry()
  .register('tf://assert/dimension_eq@0.1', args => assertDimensionEq(args))
  .register('tf://lens/mod@0.1', args => lensMod(args))
  .register('tf://assert/bounds@0.1', args => assertBounds(args))
  .register('tf://probe/delta_bounded@0.1', args => probeDeltaBounded(args))
  .register('tf://correct/saturate@0.1', args => correctSaturate(args));

export const ops = {
  assertDimensionEq,
  lensMod,
  assertBounds,
  probeDeltaBounded,
  correctSaturate,
};
