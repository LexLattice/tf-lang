export interface DiffEntry {
  readonly pointer: string;
  readonly left: unknown;
  readonly right: unknown;
}

export interface DiffOptions {
  readonly missingValue?: unknown;
}

export function diffCanonical(left: unknown, right: unknown, options: DiffOptions = {}): DiffEntry | null {
  return diffInternal(left, right, [], options.missingValue);
}

function diffInternal(
  left: unknown,
  right: unknown,
  segments: ReadonlyArray<string | number>,
  missingValue: unknown,
): DiffEntry | null {
  if (Object.is(left, right)) {
    return null;
  }

  if (left === null || right === null) {
    return { pointer: pointerFromSegments(segments), left, right };
  }

  if (Array.isArray(left) || Array.isArray(right)) {
    if (!Array.isArray(left) || !Array.isArray(right)) {
      return { pointer: pointerFromSegments(segments), left, right };
    }

    const sharedLength = Math.min(left.length, right.length);
    for (let index = 0; index < sharedLength; index += 1) {
      const child = diffInternal(left[index], right[index], [...segments, index], missingValue);
      if (child) {
        return child;
      }
    }

    if (left.length !== right.length) {
      const pointer = pointerFromSegments([...segments, sharedLength]);
      if (left.length > right.length) {
        return { pointer, left: left[sharedLength], right: missingValue };
      }
      return { pointer, left: missingValue, right: right[sharedLength] };
    }

    return null;
  }

  if (isPlainObject(left) || isPlainObject(right)) {
    if (!isPlainObject(left) || !isPlainObject(right)) {
      return { pointer: pointerFromSegments(segments), left, right };
    }

    const keys = new Set<string>([
      ...Object.keys(left as Record<string, unknown>),
      ...Object.keys(right as Record<string, unknown>),
    ]);
    const sortedKeys = Array.from(keys).sort();

    for (const key of sortedKeys) {
      const hasLeft = Object.prototype.hasOwnProperty.call(left, key);
      const hasRight = Object.prototype.hasOwnProperty.call(right, key);
      if (!hasLeft || !hasRight) {
        return {
          pointer: pointerFromSegments([...segments, key]),
          left: hasLeft ? (left as Record<string, unknown>)[key] : missingValue,
          right: hasRight ? (right as Record<string, unknown>)[key] : missingValue,
        };
      }
      const child = diffInternal(
        (left as Record<string, unknown>)[key],
        (right as Record<string, unknown>)[key],
        [...segments, key],
        missingValue,
      );
      if (child) {
        return child;
      }
    }

    return null;
  }

  return { pointer: pointerFromSegments(segments), left, right };
}

export function pointerFromSegments(segments: ReadonlyArray<string | number>): string {
  if (segments.length === 0) {
    return "";
  }
  return `/${segments.map(escapePointerSegment).join("/")}`;
}

export function escapePointerSegment(segment: string | number): string {
  return String(segment).replace(/~/g, "~0").replace(/\//g, "~1");
}

export function isPlainObject(value: unknown): value is Record<string, unknown> {
  if (typeof value !== "object" || value === null) {
    return false;
  }
  if (Array.isArray(value) || value instanceof Map || value instanceof Set) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}
