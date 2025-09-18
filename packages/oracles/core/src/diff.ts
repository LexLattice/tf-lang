export interface DiffResult {
  readonly pointer: string;
  readonly left: unknown;
  readonly right: unknown;
}

export interface DiffOptions {
  readonly missingValue?: unknown;
}

export function diffValues(left: unknown, right: unknown, options: DiffOptions = {}): DiffResult | null {
  return diffRecursive(left, right, options, []);
}

function diffRecursive(
  left: unknown,
  right: unknown,
  options: DiffOptions,
  segments: Array<string | number>,
): DiffResult | null {
  if (Object.is(left, right)) {
    return null;
  }

  if (left === null || right === null) {
    if (left === right) {
      return null;
    }
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
      const child = diffRecursive(left[index] ?? null, right[index] ?? null, options, [...segments, index]);
      if (child) {
        return child;
      }
    }
    if (left.length !== right.length) {
      const pointer = pointerFromSegments([...segments, max]);
      const missingValue = options.missingValue ?? null;
      const missingLeft = left.length > right.length ? left[max] ?? missingValue : missingValue;
      const missingRight = right.length > left.length ? right[max] ?? missingValue : missingValue;
      return {
        pointer,
        left: missingLeft,
        right: missingRight,
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
        const missingValue = options.missingValue ?? null;
        return {
          pointer: pointerFromSegments([...segments, key]),
          left: hasLeft ? (left as Record<string, unknown>)[key] : missingValue,
          right: hasRight ? (right as Record<string, unknown>)[key] : missingValue,
        };
      }
      const child = diffRecursive(
        (left as Record<string, unknown>)[key],
        (right as Record<string, unknown>)[key],
        options,
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

export function pointerFromSegments(segments: ReadonlyArray<string | number>): string {
  if (segments.length === 0) {
    return "";
  }
  return `/${segments.map(escapePointerSegment).join("/")}`;
}

export function escapePointerSegment(segment: string | number): string {
  return String(segment).replace(/~/g, "~0").replace(/\//g, "~1");
}

function isPlainObject(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}
