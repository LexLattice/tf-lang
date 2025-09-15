const FLOAT_PRECISION = 12;

type CanonicalValue =
  | null
  | boolean
  | number
  | string
  | CanonicalValue[]
  | { readonly [key: string]: CanonicalValue };

function compareCanonical(a: CanonicalValue, b: CanonicalValue): number {
  const sa = JSON.stringify(a);
  const sb = JSON.stringify(b);
  return sa.localeCompare(sb);
}

export function canonicalize(value: unknown): CanonicalValue {
  if (value === null) {
    return null;
  }
  if (typeof value === "number") {
    if (!Number.isFinite(value)) {
      return value.toString();
    }
    if (Number.isInteger(value)) {
      return value;
    }
    return value.toFixed(FLOAT_PRECISION);
  }
  if (typeof value === "bigint") {
    return value.toString();
  }
  if (typeof value === "boolean" || typeof value === "string") {
    return value;
  }
  if (Array.isArray(value)) {
    return value.map((entry) => canonicalize(entry));
  }
  if (value instanceof Date) {
    return value.toISOString();
  }
  if (value instanceof Set) {
    return Array.from(value)
      .map((entry) => canonicalize(entry))
      .sort(compareCanonical);
  }
  if (value instanceof Map) {
    const sortedEntries = Array.from(value.entries()).sort(([a], [b]) =>
      String(a).localeCompare(String(b))
    );
    const canonicalPairs = sortedEntries.map(([key, val]) => [
      String(key),
      canonicalize(val),
    ] as const);
    return canonicalize(Object.fromEntries(canonicalPairs));
  }
  if (typeof value === "object") {
    const entries = Object.entries(value as Record<string, unknown>)
      .filter(([, v]) => typeof v !== "undefined")
      .sort(([a], [b]) => a.localeCompare(b));
    const result: Record<string, CanonicalValue> = {};
    for (const [key, v] of entries) {
      result[key] = canonicalize(v);
    }
    return result;
  }
  return String(value);
}

export function canonicalJSONString(value: unknown): string {
  return JSON.stringify(canonicalize(value));
}
