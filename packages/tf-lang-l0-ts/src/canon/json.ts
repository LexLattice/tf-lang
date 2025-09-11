export function canonicalJsonBytes(value: unknown): Uint8Array {
  const json = canonical(value);
  return new TextEncoder().encode(json);
}

function canonical(v: any): string {
  if (v === null) return 'null';
  if (typeof v === 'number') {
    if (!Number.isInteger(v)) throw new Error('E_L0_FLOAT');
    return String(v);
  }
  if (typeof v === 'string') return JSON.stringify(v);
  if (typeof v === 'boolean') return v ? 'true' : 'false';
  if (Array.isArray(v)) {
    return '[' + v.map(canonical).join(',') + ']';
  }
  if (typeof v === 'object') {
    const keys = Object.keys(v).sort();
    const entries = keys.map(k => JSON.stringify(k) + ':' + canonical(v[k]));
    return '{' + entries.join(',') + '}';
  }
  throw new Error('E_JSON_TYPE');
}

