export type Canonicalizer = <T>(value: T) => T;

export const defaultCanonicalize: Canonicalizer = (value) => {
  return canonicalizeValue(value) as typeof value;
};

export function canonicalStringify(value: unknown): string {
  return JSON.stringify(canonicalizeValue(value));
}

function canonicalizeValue(value: unknown): unknown {
  if (value === null) {
    return null;
  }

  const valueType = typeof value;

  if (valueType === "number") {
    return canonicalizeNumber(value as number);
  }

  if (valueType === "string" || valueType === "boolean") {
    return value;
  }

  if (valueType === "bigint") {
    return (value as bigint).toString(10);
  }

  if (valueType === "symbol") {
    return String(value as symbol);
  }

  if (valueType === "function") {
    return `[fn ${String((value as Function).name || "anonymous")}]`;
  }

  if (Array.isArray(value)) {
    return (value as unknown[]).map((entry) => canonicalizeValue(entry ?? null));
  }

  if (value instanceof Set) {
    const canonicalItems = Array.from(value as Set<unknown>).map((entry) =>
      canonicalizeValue(entry ?? null),
    );
    canonicalItems.sort((left, right) => {
      const a = JSON.stringify(left);
      const b = JSON.stringify(right);
      if (a < b) {
        return -1;
      }
      if (a > b) {
        return 1;
      }
      return 0;
    });
    return canonicalItems;
  }

  if (value instanceof Date) {
    return value.toISOString();
  }

  if (value && typeof (value as { toJSON?: () => unknown }).toJSON === "function") {
    return canonicalizeValue((value as { toJSON: () => unknown }).toJSON());
  }

  if (value && valueType === "object") {
    const input = value as Record<string, unknown>;
    const entries = Object.entries(input)
      .filter(([, entryValue]) => entryValue !== undefined)
      .map(([key, entryValue]) => [key, canonicalizeValue(entryValue)] as const)
      .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));

    const result: Record<string, unknown> = {};
    for (const [key, entryValue] of entries) {
      result[key] = entryValue;
    }
    return result;
  }

  return value;
}

function canonicalizeNumber(value: number): number | string {
  if (!Number.isFinite(value)) {
    return value.toString();
  }

  const formatted = value.toFixed(12);
  const numeric = Number.parseFloat(formatted);
  return Object.is(numeric, -0) ? 0 : numeric;
}
