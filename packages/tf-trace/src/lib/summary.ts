import { TraceRecord } from './validate.js';

export interface TraceSummary {
  total: number;
  by_effect: Record<string, number>;
  by_prim: Record<string, number>;
  ms_total: number;
  ms_by_effect: Record<string, number>;
}

function toSortedObject(map: Map<string, number>): Record<string, number> {
  const entries = Array.from(map.entries()).sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
  const output: Record<string, number> = {};
  for (const [key, value] of entries) {
    output[key] = value;
  }
  return output;
}

export function summarizeTrace(records: TraceRecord[]): TraceSummary {
  const byEffect = new Map<string, number>();
  const byPrim = new Map<string, number>();
  const msByEffect = new Map<string, number>();
  let msTotal = 0;

  for (const record of records) {
    byEffect.set(record.effect, (byEffect.get(record.effect) ?? 0) + 1);
    byPrim.set(record.prim_id, (byPrim.get(record.prim_id) ?? 0) + 1);

    if (typeof record.ms === 'number') {
      msTotal += record.ms;
      msByEffect.set(record.effect, (msByEffect.get(record.effect) ?? 0) + record.ms);
    }
  }

  return {
    total: records.length,
    by_effect: toSortedObject(byEffect),
    by_prim: toSortedObject(byPrim),
    ms_total: msTotal,
    ms_by_effect: toSortedObject(msByEffect)
  };
}
