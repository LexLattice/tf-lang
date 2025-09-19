export const MISSING_VALUE = "[missing]" as const;

export interface DiffEntry {
  readonly pointer: string;
  readonly left: unknown;
  readonly right: unknown;
}

export function escapePointerSegment(segment: string | number): string {
  return String(segment).replace(/~/g, "~0").replace(/\//g, "~1");
}

export function pointerFromSegments(segments: ReadonlyArray<string | number>): string {
  if (segments.length === 0) {
    return "";
  }
  return `/${segments.map(escapePointerSegment).join("/")}`;
}

export function isPlainObject(value: unknown): value is Record<string, unknown> {
  if (value === null || typeof value !== "object") {
    return false;
  }
  if (Array.isArray(value) || value instanceof Map || value instanceof Set || value instanceof Date) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

export function diffCanonical(
  left: unknown,
  right: unknown,
  segments: ReadonlyArray<string | number> = [],
): DiffEntry | null {
  if (Object.is(left, right)) {
    return null;
  }

  if (left === null || right === null) {
    return {
      pointer: pointerFromSegments(segments),
      left,
      right,
    };
  }

  if (Array.isArray(left) || Array.isArray(right)) {
    if (!Array.isArray(left) || !Array.isArray(right)) {
      return {
        pointer: pointerFromSegments(segments),
        left,
        right,
      };
    }

    const max = Math.min(left.length, right.length);
    for (let index = 0; index < max; index += 1) {
      const child = diffCanonical(left[index], right[index], [...segments, index]);
      if (child) {
        return child;
      }
    }

    if (left.length !== right.length) {
      const pointer = pointerFromSegments([...segments, max]);
      const hasLeft = max < left.length;
      const hasRight = max < right.length;
      return {
        pointer,
        left: hasLeft ? left[max] : MISSING_VALUE,
        right: hasRight ? right[max] : MISSING_VALUE,
      };
    }

    return null;
  }

  if (isPlainObject(left) || isPlainObject(right)) {
    if (!isPlainObject(left) || !isPlainObject(right)) {
      return {
        pointer: pointerFromSegments(segments),
        left,
        right,
      };
    }

    const keys = Array.from(new Set([...Object.keys(left), ...Object.keys(right)])).sort();
    for (const key of keys) {
      const hasLeft = Object.prototype.hasOwnProperty.call(left, key);
      const hasRight = Object.prototype.hasOwnProperty.call(right, key);
      if (!hasLeft || !hasRight) {
        return {
          pointer: pointerFromSegments([...segments, key]),
          left: hasLeft ? (left as Record<string, unknown>)[key] : MISSING_VALUE,
          right: hasRight ? (right as Record<string, unknown>)[key] : MISSING_VALUE,
        };
      }
      const child = diffCanonical(
        (left as Record<string, unknown>)[key],
        (right as Record<string, unknown>)[key],
        [...segments, key],
      );
      if (child) {
        return child;
      }
    }

    return null;
  }

  return {
    pointer: pointerFromSegments(segments),
    left,
    right,
  };
}
