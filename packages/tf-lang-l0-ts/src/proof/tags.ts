export type Delta = null | { replace: unknown };
export interface Effect {
  read: string[];
  write: string[];
  external: string[];
}

export interface Witness {
  kind: 'Witness';
  delta: Delta;
  effect: Effect;
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
