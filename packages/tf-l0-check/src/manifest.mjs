export function manifestFromVerdict(verdict = {}) {
  const uniq = (xs = []) => Array.from(new Set(xs)).sort();
  const dedupeObjArray = (arr = []) =>
    Array.from(new Map(arr.map((o) => [JSON.stringify(o), o])).values());

  return {
    required_effects: uniq(verdict.effects || []),
    footprints: {
      reads: dedupeObjArray(verdict.reads || []),
      writes: dedupeObjArray(verdict.writes || [])
    },
    qos: verdict.qos || {}
  };
}
