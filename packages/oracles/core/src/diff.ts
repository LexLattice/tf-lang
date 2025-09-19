export interface DiffResult {
  readonly pointer: string;
  readonly left: unknown;
  readonly right: unknown;
}

export interface DiffOptions {
  readonly segments?: ReadonlyArray<string | number>;
  readonly missingValue?: unknown;
}

export function diffValues(left: unknown, right: unknown, options: DiffOptions = {}): DiffResult | null {
  if (Object.is(left, right)) {
    return null;
  }

  const segments = options.segments ? [...options.segments] : [];
  const missingValue = options.missingValue;

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
      const child = diffValues(left[index], right[index], {
        segments: [...segments, index],
        missingValue,
      });
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
        left: hasLeft ? left[max] : missingValue,
        right: hasRight ? right[max] : missingValue,
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

    const keys = new Set<string>();
    for (const key of Object.keys(left as Record<string, unknown>)) {
      keys.add(key);
    }
    for (const key of Object.keys(right as Record<string, unknown>)) {
      keys.add(key);
    }
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

      const child = diffValues((left as Record<string, unknown>)[key], (right as Record<string, unknown>)[key], {
        segments: [...segments, key],
        missingValue,
      });
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

export function isPlainObject(value: unknown): value is Record<string, unknown> {
  if (typeof value !== "object" || value === null) {
    return false;
  }

  if (Array.isArray(value)) {
    return false;
  }

  const prototype = Object.getPrototypeOf(value);
  return prototype === null || prototype === Object.prototype;
}
