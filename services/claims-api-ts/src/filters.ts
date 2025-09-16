import type { Filters, Modality } from './types.js';

const MODALITIES: Modality[] = ['FORBIDDEN', 'PERMITTED', 'OBLIGATORY', 'EXEMPT', 'EXCEPTION'];

export function parseFilters(q: Record<string, unknown>): Filters {
  const f: Filters = {};
  if (q.modality !== undefined) {
    if (typeof q.modality !== 'string' || !MODALITIES.includes(q.modality as Modality)) {
      throw new Error('bad_modality');
    }
    f.modality = q.modality as Modality;
  }
  if (q.jurisdiction !== undefined) {
    if (typeof q.jurisdiction !== 'string') throw new Error('bad_jurisdiction');
    f.jurisdiction = q.jurisdiction;
  }
  if (q.at !== undefined) {
    if (typeof q.at !== 'string' || !/^\d{4}-\d{2}-\d{2}$/.test(q.at)) throw new Error('bad_at');
    f.at = q.at;
  }
  if (q.limit !== undefined) {
    const n = Number(q.limit);
    if (!Number.isInteger(n) || n < 0 || n > 200) throw new Error('bad_limit');
    f.limit = n;
  }
  if (q.offset !== undefined) {
    const n = Number(q.offset);
    if (!Number.isInteger(n) || n < 0) throw new Error('bad_offset');
    f.offset = n;
  }
  return f;
}

export function filtersToRecord(filters: Filters): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  if (filters.modality !== undefined) out.modality = filters.modality;
  if (filters.jurisdiction !== undefined) out.jurisdiction = filters.jurisdiction;
  if (filters.at !== undefined) out.at = filters.at;
  if (filters.limit !== undefined) out.limit = filters.limit;
  if (filters.offset !== undefined) out.offset = filters.offset;
  return out;
}
