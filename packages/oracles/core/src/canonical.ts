const collator = new Intl.Collator("en", { sensitivity: "variant" });

const sortKeys = (entries: readonly [string, unknown][]): [string, unknown][] =>
  [...entries].sort((a, b) => collator.compare(a[0], b[0]));

const canonicalPrimitive = (value: unknown): unknown => {
  if (typeof value === "number" && !Number.isFinite(value)) {
    return null;
  }
  if (Number.isNaN(value)) return null;
  if (value === undefined) return null;
  return value;
};

const isPlainObject = (value: object): boolean => {
  const proto = Object.getPrototypeOf(value);
  return proto === null || proto === Object.prototype;
};

const canonicalizeUnknown = (value: unknown): unknown => {
  if (value === null) return null;
  if (typeof value === "object") {
    if (Array.isArray(value)) {
      return value.map((item) => canonicalizeUnknown(item));
    }
    if (value instanceof Date) {
      return value.toISOString();
    }
    if (value instanceof Set) {
      const items = [...value].map((item) => canonicalizeUnknown(item));
      const withKeys = items.map((item) => ({
        key: JSON.stringify(item),
        value: item,
      }));
      return sortKeys(withKeys.map(({ key, value }) => [key, value])).map(
        ([, canonical]) => canonical,
      );
    }
    if (value instanceof Map) {
      const mapped = Array.from(value.entries()).map(([k, v]) => [
        String(k),
        canonicalizeUnknown(v),
      ] as [string, unknown]);
      return sortKeys(mapped).map(([k, v]) => ({ key: k, value: v }));
    }
    if (isPlainObject(value)) {
      const entries = Object.entries(value as Record<string, unknown>);
      const filtered: [string, unknown][] = [];
      for (const [key, v] of entries) {
        if (typeof v === "undefined") continue;
        filtered.push([key, canonicalizeUnknown(v)]);
      }
      const sorted = sortKeys(filtered);
      const result: Record<string, unknown> = {};
      for (const [key, v] of sorted) {
        result[key] = v;
      }
      return result;
    }
    return canonicalPrimitive(value);
  }
  return canonicalPrimitive(value);
};

export const canonicalize = <T>(value: T): T => canonicalizeUnknown(value) as T;

export const canonicalStringify = (value: unknown): string =>
  JSON.stringify(canonicalizeUnknown(value));

export const canonicalBuffer = (value: unknown): Uint8Array =>
  new TextEncoder().encode(canonicalStringify(value));

