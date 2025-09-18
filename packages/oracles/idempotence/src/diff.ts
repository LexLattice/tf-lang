import type { IdempotenceMismatch } from "./types.js";

export function diffCanonical(
  left: unknown,
  right: unknown,
): IdempotenceMismatch | undefined {
  return visit(left, right, "");
}

function visit(
  left: unknown,
  right: unknown,
  pointer: string,
): IdempotenceMismatch | undefined {
  if (Object.is(left, right)) {
    return undefined;
  }

  const leftType = typeOf(left);
  const rightType = typeOf(right);

  if (leftType !== rightType) {
    return mismatch(pointer, left, right);
  }

  if (leftType === "array") {
    return diffArray(left as unknown[], right as unknown[], pointer);
  }

  if (leftType === "object") {
    return diffObject(left as Record<string, unknown>, right as Record<string, unknown>, pointer);
  }

  return mismatch(pointer, left, right);
}

function diffArray(
  left: unknown[],
  right: unknown[],
  pointer: string,
): IdempotenceMismatch | undefined {
  const limit = Math.min(left.length, right.length);
  for (let index = 0; index < limit; index += 1) {
    const childPointer = `${pointer}/${escapeSegment(String(index))}`;
    const result = visit(left[index], right[index], childPointer);
    if (result) {
      return result;
    }
  }

  if (left.length !== right.length) {
    const index = limit;
    const childPointer = `${pointer}/${escapeSegment(String(index))}`;
    return mismatch(childPointer, left[index], right[index]);
  }

  return undefined;
}

function diffObject(
  left: Record<string, unknown>,
  right: Record<string, unknown>,
  pointer: string,
): IdempotenceMismatch | undefined {
  const keys = new Set([...Object.keys(left), ...Object.keys(right)]);
  const orderedKeys = Array.from(keys.values()).sort();
  for (const key of orderedKeys) {
    const childPointer = `${pointer}/${escapeSegment(key)}`;
    if (!(key in left)) {
      return mismatch(childPointer, undefined, right[key]);
    }
    if (!(key in right)) {
      return mismatch(childPointer, left[key], undefined);
    }
    const result = visit(left[key], right[key], childPointer);
    if (result) {
      return result;
    }
  }
  return undefined;
}

function typeOf(value: unknown): "null" | "array" | "object" | string {
  if (value === null) return "null";
  if (Array.isArray(value)) return "array";
  if (typeof value === "object") return "object";
  return typeof value;
}

function escapeSegment(segment: string): string {
  return segment.replace(/~/g, "~0").replace(/\//g, "~1");
}

function mismatch(
  pointer: string,
  left: unknown,
  right: unknown,
): IdempotenceMismatch {
  return { pointer: pointer || "/", left, right };
}
