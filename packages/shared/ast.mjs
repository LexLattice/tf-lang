export function collectVarRefs(value, refs = new Set()) {
  if (typeof value === 'string') {
    if (value.startsWith('@')) {
      const ref = value.slice(1);
      if (ref.length > 0) {
        refs.add(ref.split('.')[0]);
      }
    }
    return refs;
  }
  if (Array.isArray(value)) {
    for (const item of value) {
      collectVarRefs(item, refs);
    }
    return refs;
  }
  if (value && typeof value === 'object') {
    for (const nested of Object.values(value)) {
      collectVarRefs(nested, refs);
    }
  }
  return refs;
}

export function collectVarRefsArray(value) {
  return Array.from(collectVarRefs(value));
}

