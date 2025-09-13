
export type Modality = 'FORBIDDEN' | 'PERMITTED' | 'OBLIGATORY' | 'EXEMPT' | 'EXCEPTION';
export interface Filters {
  modality?: Modality;
  jurisdiction?: string;
  at?: string; // ISO date
  limit?: number;
  offset?: number;
}

export interface Evidence {
  hash: string;
  [k: string]: unknown;
}

export interface Claim {
  id: string;
  evidence: Evidence[];
  explanation?: string | null;
  [k: string]: unknown;
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
