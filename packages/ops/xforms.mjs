import { stableStringify, hashBlake3 } from '../util/encoding.mjs';

function isPlainObject(value) {
  if (!value || typeof value !== 'object') return false;
  if (Array.isArray(value)) return false;
  if (value instanceof Uint8Array) return false;
  if (value instanceof ArrayBuffer) return false;
  if (Buffer.isBuffer?.(value)) return false;
  return true;
}

function cloneValue(value) {
  if (Array.isArray(value)) {
    return value.map((item) => cloneValue(item));
  }
  if (isPlainObject(value)) {
    const out = {};
    for (const [key, val] of Object.entries(value)) {
      out[key] = cloneValue(val);
    }
    return out;
  }
  return value;
}

function decodePointerSegment(segment) {
  return segment.replace(/~1/g, '/').replace(/~0/g, '~');
}

/**
 * NOTE: This is a *restricted* JSON Patch.
 * - Only object paths are supported (no array ops).
 * - Root document replacement (path: "") is *not* supported (RFC 6902 allows it; we reject it to keep transforms pure and localized).
 * - Operations: add | replace | remove.
 * Inputs are never mutated; returns a new object.
 */
export function applyJsonPatch(base = {}, operations = []) {
  if (!isPlainObject(base)) {
    throw new Error('jsonpatch.apply: base document must be a plain object');
  }
  if (!Array.isArray(operations)) {
    throw new Error('jsonpatch.apply: patch must be an array of operations');
  }

  let result = cloneValue(base);

  const ensureContainer = (container, path) => {
    if (!isPlainObject(container)) {
      throw new Error(`jsonpatch.apply: path ${path} does not reference an object`);
    }
    return container;
  };

  operations.forEach((operation, index) => {
    if (!operation || typeof operation !== 'object') {
      throw new Error(`jsonpatch.apply: operation at index ${index} must be an object`);
    }
    const type = operation.op;
    if (!['add', 'replace', 'remove'].includes(type)) {
      throw new Error(`jsonpatch.apply: unsupported op "${type}" at index ${index}`);
    }
    const path = typeof operation.path === 'string' ? operation.path : '';
    const segments = path === ''
      ? []
      : path
        .split('/')
        .slice(1)
        .map((segment) => decodePointerSegment(segment));

    if (segments.length === 0) {
      throw new Error('jsonpatch.apply: root operations are not supported by this implementation');
    }

    let cursor = result;
    for (let i = 0; i < segments.length - 1; i += 1) {
      const key = segments[i];
      if (!Object.prototype.hasOwnProperty.call(cursor, key) || cursor[key] === undefined) {
        if (type === 'add') {
          cursor[key] = {};
        } else {
          throw new Error(`jsonpatch.apply: missing path segment "${key}" for op at index ${index}`);
        }
      }
      cursor[key] = ensureContainer(cursor[key], path);
      cursor = cursor[key];
    }

    const leaf = segments[segments.length - 1];
    cursor = ensureContainer(cursor, path);

    if (type === 'remove') {
      delete cursor[leaf];
      return;
    }

    cursor[leaf] = cloneValue(operation.value);
  });

  return result;
}

export function mergeGCounter(base = {}, patch = {}) {
  const counts = {};
  const keys = new Set([...Object.keys(base || {}), ...Object.keys(patch || {})]);
  for (const key of keys) {
    const left = Number(base?.[key] ?? 0);
    const right = Number(patch?.[key] ?? 0);
    counts[key] = Math.max(left, right);
  }
  const total = Object.values(counts).reduce((sum, value) => sum + Number(value ?? 0), 0);
  return { counts, total };
}

export function parseTimestampInput(value) {
  if (value === undefined || value === null) {
    throw new Error('time.parseTimestamp: value is required');
  }
  if (value instanceof Date) {
    return value.getTime();
  }
  if (typeof value === 'number') {
    return value;
  }
  if (typeof value === 'string') {
    const parsed = Date.parse(value);
    if (Number.isNaN(parsed)) {
      throw new Error(`time.parseTimestamp: unable to parse "${value}"`);
    }
    return parsed;
  }
  throw new Error(`time.parseTimestamp: unsupported value type ${typeof value}`);
}

const UNIT_MS = {
  millisecond: 1,
  second: 1000,
  minute: 60 * 1000,
  hour: 60 * 60 * 1000,
  day: 24 * 60 * 60 * 1000,
};

export function resolveIntervalMs(spec = {}) {
  if (spec.interval_ms !== undefined) {
    const value = Number(spec.interval_ms);
    if (!Number.isFinite(value) || value <= 0) {
      throw new Error('time.align: interval_ms must be a positive number');
    }
    return value;
  }
  const unit = spec.unit || spec.granularity || 'minute';
  const base = UNIT_MS[unit];
  if (!base) {
    throw new Error(`time.align: unsupported unit "${unit}"`);
  }
  const step = spec.step !== undefined ? Number(spec.step) : 1;
  if (!Number.isFinite(step) || step <= 0) {
    throw new Error('time.align: step must be a positive number');
  }
  return base * step;
}

export function alignTimestamp(timestampMs, intervalMs) {
  return Math.floor(timestampMs / intervalMs) * intervalMs;
}

export function formatIso(epochMs) {
  return new Date(epochMs).toISOString();
}

export function computeSagaId(steps = [], compensations = []) {
  const payload = stableStringify({ steps, compensations });
  return hashBlake3(payload);
}

export function cloneDeep(value) {
  return cloneValue(value);
}

export function isObjectLike(value) {
  return isPlainObject(value);
}
