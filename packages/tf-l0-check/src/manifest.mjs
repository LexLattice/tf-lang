const uniq = (xs = []) => Array.from(new Set(xs)).sort();

function stableStringify(value) {
  if (Array.isArray(value)) {
    return `[${value.map(stableStringify).join(',')}]`;
  }
  if (value && typeof value === 'object') {
    const keys = Object.keys(value).sort();
    return `{${keys
      .map((key) => `${JSON.stringify(key)}:${stableStringify(value[key])}`)
      .join(',')}}`;
  }
  return JSON.stringify(value);
}

const dedupeObjArray = (arr = []) =>
  Array.from(new Set(arr.map(stableStringify)))
    .sort()
    .map((serialized) => JSON.parse(serialized));

export function manifestFromVerdict(verdict = {}) {
  const reads = dedupeObjArray(verdict.reads || []);
  const writes = dedupeObjArray(verdict.writes || []);
  const required_effects = uniq(verdict.effects || []);

  return {
    // legacy (schema v0.3)
    effects: required_effects,
    scopes: [],
    footprints: dedupeObjArray([...(verdict.reads || []), ...(verdict.writes || [])]),
    // new (v0.4)
    required_effects,
    footprints_rw: { reads, writes },
    qos: verdict.qos || {}
  };
}
