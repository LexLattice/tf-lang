export function deepClone(value) {
  if (value === null || typeof value !== 'object') {
    return value;
  }
  if (Array.isArray(value)) {
    return value.map((item) => deepClone(item));
  }
  const out = {};
  for (const [key, val] of Object.entries(value)) {
    out[key] = deepClone(val);
  }
  return out;
}

export default deepClone;
