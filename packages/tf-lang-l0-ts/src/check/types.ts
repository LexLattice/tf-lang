
import type { Program } from '../model/bytecode.js';
import { Effects } from '../model/types.js';

export interface CheckReport {
  ok: boolean;
  observed: Effects;
  declared: Effects;
  messages: string[];
}

export function typeAndEffectCheck(_prog: Program, declared: Effects): CheckReport {
  // TODO: SSA, type inference, exhaustiveness, effect accounting.
  return {
    ok: true,
    observed: declared,
    declared,
    messages: ['checker stub: always ok'],
  };
}
