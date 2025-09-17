export type Canonicalizer = (value: unknown) => unknown;
export type DeepEqualResult = { ok: true } | { ok: false; path: string };

export type PointerSegment = string | number;

const DUPLICATE_LABEL_CODE = "E_DUPLICATE_KEY_LABEL" as const;

export class CanonicalizeError extends Error {
  readonly code = DUPLICATE_LABEL_CODE;
  readonly label: string;

  constructor(label: string) {
    super(`duplicate canonical key label: ${label}`);
    this.name = "CanonicalizeError";
    this.label = label;
  }
}

export function canonicalize(value: unknown): unknown {
  return canonicalizeInner(value);
}

export function canonicalJson(value: unknown): string {
  const canonical = canonicalize(value);
  return `${JSON.stringify(canonical)}\n`;
}

export function prettyCanonicalJson(value: unknown): string {
  const canonical = canonicalize(value);
  return `${JSON.stringify(canonical, null, 2)}\n`;
}

export function deepEqual(left: unknown, right: unknown): DeepEqualResult {
  const canonicalLeft = canonicalize(left);
  const canonicalRight = canonicalize(right);
  const diff = diffCanonical(canonicalLeft, canonicalRight, []);
  if (diff === null) {
    return { ok: true };
  }
  return { ok: false, path: pointerFromSegments(diff) };
}

export function pointerFromSegments(segments: PointerSegment[]): string {
  if (segments.length === 0) {
    return "/";
  }
  return `/${segments.map((segment) => escapePointerSegment(String(segment))).join("/")}`;
}

export function segmentsFromPointer(pointer: string): PointerSegment[] {
  if (pointer.length === 0 || pointer === "/") {
    return [];
  }
  if (!pointer.startsWith("/")) {
    throw new Error(`invalid pointer: ${pointer}`);
  }
  const tail = pointer.slice(1);
  if (tail.length === 0) {
    return [];
  }
  const segments = tail.split("/").map(unescapePointerSegment);
  return segments.map(parsePointerSegment);
}

function canonicalizeInner(value: unknown): unknown {
  if (value === null) {
    return null;
  }

  if (value === undefined) {
    throw new TypeError("cannot canonicalize undefined");
  }

  if (typeof value === "number") {
    return canonicalizeNumber(value);
  }

  if (typeof value === "string" || typeof value === "boolean") {
    return value;
  }

  if (typeof value === "bigint") {
    throw new TypeError("cannot canonicalize bigint");
  }

  if (typeof value === "symbol") {
    throw new TypeError("cannot canonicalize symbol");
  }

  if (typeof value === "function") {
    throw new TypeError("cannot canonicalize function");
  }

  if (Array.isArray(value)) {
    return value.map((entry) => canonicalizeInner(entry));
  }

  if (value instanceof Set) {
    return canonicalizeSet(value);
  }

  if (value instanceof Map) {
    return canonicalizeMap(value);
  }

  if (value instanceof Date) {
    throw new TypeError("cannot canonicalize Date");
  }

  if (isArrayBufferView(value)) {
    return canonicalizeArrayBufferView(value);
  }

  if (isArrayBufferValue(value)) {
    return canonicalizeArrayBuffer(value);
  }

  if (isPlainObject(value)) {
    return canonicalizeObject(value as Record<string, unknown>);
  }

  throw new TypeError(`cannot canonicalize value of type ${typeof value}`);
}

function canonicalizeNumber(value: number): number | string {
  if (!Number.isFinite(value)) {
    return value.toString();
  }
  const formatted = Number.parseFloat(value.toFixed(12));
  return Object.is(formatted, -0) ? 0 : formatted;
}

function canonicalizeSet(set: Set<unknown>): unknown[] {
  const entries = Array.from(set.values()).map((entry) => {
    const canonicalValue = canonicalizeInner(entry);
    const label = canonicalLabelFromCanonicalValue(canonicalValue);
    return { label, value: canonicalValue };
  });
  entries.sort((a, b) => compareLabels(a.label, b.label));
  return entries.map((entry) => entry.value);
}

function canonicalizeMap(map: Map<unknown, unknown>): Array<{ label: string; value: unknown }> {
  const seen = new Set<string>();
  const entries = Array.from(map.entries()).map(([key, value]) => {
    const canonicalKey = canonicalizeInner(key);
    const label = canonicalLabelFromCanonicalValue(canonicalKey);
    if (seen.has(label)) {
      throw new CanonicalizeError(label);
    }
    seen.add(label);
    const canonicalValue = canonicalizeInner(value);
    return { label, value: canonicalValue };
  });
  entries.sort((a, b) => compareLabels(a.label, b.label));
  return entries;
}

function canonicalizeObject(value: Record<string, unknown>): Record<string, unknown> {
  const entries = Object.entries(value)
    .map(([key, entryValue]) => {
      if (entryValue === undefined) {
        throw new TypeError(`cannot canonicalize undefined at key ${key}`);
      }
      return [key, canonicalizeInner(entryValue)] as const;
    })
    .sort(([a], [b]) => compareLabels(a, b));

  const result: Record<string, unknown> = {};
  for (const [key, entryValue] of entries) {
    result[key] = entryValue;
  }
  return result;
}

function canonicalizeArrayBuffer(buffer: ArrayBufferLike): number[] {
  return Array.from(new Uint8Array(buffer));
}

function canonicalizeArrayBufferView(view: ArrayBufferView): number[] {
  return Array.from(new Uint8Array(view.buffer, view.byteOffset, view.byteLength));
}

function canonicalLabelFromCanonicalValue(value: unknown): string {
  return `${JSON.stringify(value)}\n`;
}

function compareLabels(a: string, b: string): number {
  if (a < b) {
    return -1;
  }
  if (a > b) {
    return 1;
  }
  return 0;
}

function diffCanonical(left: unknown, right: unknown, path: PointerSegment[]): PointerSegment[] | null {
  if (Object.is(left, right)) {
    return null;
  }

  if (left === null || right === null) {
    return path;
  }

  if (typeof left !== typeof right) {
    return path;
  }

  if (Array.isArray(left) && Array.isArray(right)) {
    const minLength = Math.min(left.length, right.length);
    for (let index = 0; index < minLength; index += 1) {
      const diff = diffCanonical(left[index], right[index], [...path, index]);
      if (diff !== null) {
        return diff;
      }
    }
    if (left.length !== right.length) {
      return [...path, minLength];
    }
    return null;
  }

  if (isPlainObject(left) && isPlainObject(right)) {
    const leftKeys = Object.keys(left as Record<string, unknown>);
    const rightKeys = Object.keys(right as Record<string, unknown>);
    const allKeys = Array.from(new Set([...leftKeys, ...rightKeys])).sort(compareLabels);
    for (const key of allKeys) {
      const leftHas = Object.prototype.hasOwnProperty.call(left, key);
      const rightHas = Object.prototype.hasOwnProperty.call(right, key);
      if (!leftHas || !rightHas) {
        return [...path, key];
      }
      const diff = diffCanonical(
        (left as Record<string, unknown>)[key],
        (right as Record<string, unknown>)[key],
        [...path, key],
      );
      if (diff !== null) {
        return diff;
      }
    }
    return null;
  }

  return path;
}

function escapePointerSegment(segment: string): string {
  return segment.replace(/~/g, "~0").replace(/\//g, "~1");
}

function unescapePointerSegment(segment: string): string {
  return segment.replace(/~1/g, "/").replace(/~0/g, "~");
}

function parsePointerSegment(segment: string): PointerSegment {
  if (segment === "") {
    return "";
  }
  if (/^(0|[1-9][0-9]*)$/.test(segment)) {
    const numeric = Number(segment);
    if (Number.isSafeInteger(numeric)) {
      return numeric;
    }
  }
  return segment;
}

function isPlainObject(value: unknown): value is Record<string, unknown> {
  if (value === null || typeof value !== "object") {
    return false;
  }
  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}

function isArrayBufferView(value: unknown): value is ArrayBufferView {
  return typeof ArrayBuffer !== "undefined" && ArrayBuffer.isView(value as ArrayBufferView);
}

function isArrayBufferValue(value: unknown): value is ArrayBufferLike {
  if (typeof ArrayBuffer !== "undefined" && value instanceof ArrayBuffer) {
    return true;
  }
  return typeof SharedArrayBuffer !== "undefined" && value instanceof SharedArrayBuffer;
}
