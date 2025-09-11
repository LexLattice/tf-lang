import type { Effects, Value } from '../model/types.js';

export interface Witness {
  kind: 'Witness';
  delta: Value;
  effect: Effects;
}

export interface Normalization {
  kind: 'Normalization';
  target: 'delta' | 'effect' | 'state';
}

export interface Transport {
  kind: 'Transport';
  op: 'LENS_PROJ' | 'LENS_MERGE';
  region: string;
}

export interface Refutation {
  kind: 'Refutation';
  code: string;
  msg?: string;
}

export interface Conservativity {
  kind: 'Conservativity';
  callee: string;
  expected: string;
  found: string;
}

export type ProofTag =
  | Witness
  | Normalization
  | Transport
  | Refutation
  | Conservativity;
