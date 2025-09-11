export type DeltaNF = null | { replace: unknown };
export interface EffectNF { read: string[]; write: string[]; external: string[] }

export type NormalizationTarget = 'delta' | 'effect' | 'state';
export type TransportOp = 'LENS_PROJ' | 'LENS_MERGE';

export interface Witness { kind: 'Witness'; delta: DeltaNF; effect: EffectNF }
export interface Normalization { kind: 'Normalization'; target: NormalizationTarget }
export interface Transport { kind: 'Transport'; op: TransportOp; region: string }
export interface Refutation { kind: 'Refutation'; code: string; msg?: string }
export interface Conservativity { kind: 'Conservativity'; callee: string; expected: string; found: string }

export type ProofTag = Witness | Normalization | Transport | Refutation | Conservativity;
