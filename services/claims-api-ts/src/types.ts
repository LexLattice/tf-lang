
export type Modality = 'FORBIDDEN' | 'PERMITTED' | 'OBLIGATORY' | 'EXEMPT' | 'EXCEPTION';
export interface Filters {
  modality?: Modality;
  jurisdiction?: string;
  at?: string; // ISO date
  limit?: number;
  offset?: number;
}
