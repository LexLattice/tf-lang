
export type Modality = 'FORBIDDEN' | 'PERMITTED' | 'OBLIGATORY' | 'EXEMPT' | 'EXCEPTION';
export type Status = 'determinate' | 'ambiguous' | 'contradictory';

export interface Scope {
  subject?: string;
  action?: string;
  object?: string;
  conditions?: string;
  jurisdiction?: string;
}

export interface Evidence {
  source_uri: string;
  span: [number, number] | null;
  hash: string;
  rule_id: string;
  precedence?: string;
}

export interface Claim {
  id: string;
  kind: 'DEONTIC' | 'POLICY' | 'BUILD_RULE' | string;
  modality: Modality;
  scope: Scope;
  effective: { from: string; to?: string | null };
  status: Status;
  explanation?: { why?: string; choice_points?: string[]; conflicts?: string[] };
  evidence: Evidence[];
  dataset_version: string;
  query_hash: string;
}

export type PrecedenceOrder = '<' | '>' | '=' | '⊥';

export interface PrecedenceCtx {
  policy: 'legal' | 'generic';
  now?: string;
}

export interface PrecedenceFn {
  (a: Claim, b: Claim, ctx: PrecedenceCtx): PrecedenceOrder;
}
