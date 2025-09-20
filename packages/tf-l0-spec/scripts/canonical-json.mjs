export function canonicalize(value) {
  return JSON.stringify(sortKeys(value));
}
function sortKeys(v) {
  if (v === null || typeof v !== 'object') return v;
  if (Array.isArray(v)) return v.map(sortKeys);
  const out = {};
  for (const k of Object.keys(v).sort()) out[k] = sortKeys(v[k]);
  return out;
}
