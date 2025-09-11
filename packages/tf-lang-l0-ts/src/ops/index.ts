import { dimension_eq } from './dimension_eq.js';
import { lens_mod } from './lens_mod.js';
import { assert_bounds } from './bounds.js';
import { delta_bounded } from './delta_bounded.js';
import { saturate } from './saturate.js';

export const ops: Record<string, (...args: any[]) => any> = {
  'tf://assert/dimension_eq@0.1': dimension_eq,
  'tf://lens/mod@0.1': lens_mod,
  'tf://assert/bounds@0.1': assert_bounds,
  'tf://probe/delta_bounded@0.1': delta_bounded,
  'tf://correct/saturate@0.1': saturate,
};
