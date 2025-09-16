
export type Modality = 'FORBIDDEN' | 'PERMITTED' | 'OBLIGATORY' | 'EXEMPT' | 'EXCEPTION';
export interface Filters {
  modality?: Modality;
  jurisdiction?: string;
  at?: string; // ISO date
  limit?: number;
  offset?: number;
}

export interface Evidence {
  source_uri: string;
  span: string | null;
  hash: string;
  rule_id: string;
}

export interface Claim {
  id: string;
  evidence: Evidence[];
  explanation?: string | null;
  [k: string]: unknown;
}

export interface CountResult {
  dataset_version: string;
  query_hash: string;
  filters: Filters;
  n: number;
  samples: Evidence[];
}

export interface ListResult {
  dataset_version: string;
  query_hash: string;
  filters: Filters;
  total: number;
  items: Claim[];
}
