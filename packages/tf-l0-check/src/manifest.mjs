export function manifestFromVerdict(v) {
  const uniq = (xs = []) => Array.from(new Set(xs)).sort();
  const dedupeObjArray = (arr = []) => {
    const unique = Array.from(new Map(arr.map((o) => [JSON.stringify(o), o])).values());
    return unique.sort((a, b) => {
      const sa = JSON.stringify(a);
      const sb = JSON.stringify(b);
      return sa.localeCompare(sb);
    });
  };

  return {
    required_effects: uniq(v.effects || []),
    footprints: {
      reads: dedupeObjArray(v.reads || []),
      writes: dedupeObjArray(v.writes || []),
    },
    qos: v.qos || {},
  };
}
