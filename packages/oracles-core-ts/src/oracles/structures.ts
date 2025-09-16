export function normalizeForComparison(value: unknown): unknown {
  if (value === null || typeof value !== "object") {
    return value;
  }

  if (value instanceof Map) {
    const entries = Array.from(value.entries()).map(([key, val]) => {
      const normalizedKey = normalizeForComparison(key);
      const normalizedValue = normalizeForComparison(val);
      return [normalizedKey, normalizedValue] as [unknown, unknown];
    });
    entries.sort((a, b) => compareNormalized(a[0], b[0]));
    return { __map__: entries };
  }

  if (value instanceof Set) {
    const entries = Array.from(value.values()).map(entry => normalizeForComparison(entry));
    entries.sort(compareNormalized);
    return { __set__: entries };
  }

  if (Array.isArray(value)) {
    return value.map(normalizeForComparison);
  }

  const asRecord = value as Record<string, unknown>;
  const sortedKeys = Object.keys(asRecord).sort();
  const result: Record<string, unknown> = {};
  for (const key of sortedKeys) {
    result[key] = normalizeForComparison(asRecord[key]);
  }
  return result;
}

function compareNormalized(a: unknown, b: unknown): number {
  const sa = JSON.stringify(a);
  const sb = JSON.stringify(b);
  if (sa < sb) return -1;
  if (sa > sb) return 1;
  return 0;
}

export function canonicalLabel(value: unknown): string {
  return JSON.stringify(normalizeForComparison(value));
}

export interface SortedMapEntry {
  key: unknown;
  value: unknown;
  label: string;
}

export function sortMapEntries(map: Map<unknown, unknown>): SortedMapEntry[] {
  return Array.from(map.entries())
    .map(([key, value]) => ({ key, value, label: canonicalLabel(key) }))
    .sort((a, b) => a.label.localeCompare(b.label));
}

export interface SortedSetEntry {
  value: unknown;
  label: string;
}

export function sortSetValues(set: Set<unknown>): SortedSetEntry[] {
  return Array.from(set.values())
    .map(value => ({ value, label: canonicalLabel(value) }))
    .sort((a, b) => a.label.localeCompare(b.label));
}

export function isPlainObject(value: unknown): value is Record<string, unknown> {
  return (
    value !== null &&
    typeof value === "object" &&
    !Array.isArray(value) &&
    !(value instanceof Map) &&
    !(value instanceof Set)
  );
}
