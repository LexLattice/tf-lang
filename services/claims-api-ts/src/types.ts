
export type Modality =
  | 'FORBIDDEN'
  | 'PERMITTED'
  | 'OBLIGATORY'
  | 'EXEMPT'
  | 'EXCEPTION';

export interface Filters {
  modality?: Modality;
  jurisdiction?: string;
  at?: string; // ISO date
  limit?: number;
  offset?: number;
}

export interface Evidence {
  source_uri: string;
  span: unknown;
  hash: string;
  rule_id?: string;
}

export interface Claim {
  id: string;
  modality: Modality;
  jurisdiction: string;
  effective: { from: string; to: string | null };
  status: string;
  evidence: Evidence[];
  explanation?: string | null;
  [key: string]: unknown;
}

export interface CountResponse {
  dataset_version: string;
  query_hash: string;
  filters: Filters;
  n: number;
  samples: Evidence[];
}

export interface ListResponse {
  dataset_version: string;
  query_hash: string;
  filters: Filters;
  total: number;
  items: Claim[];
}
