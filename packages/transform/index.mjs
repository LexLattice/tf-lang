import Ajv from 'ajv';
import {
  stableStringify,
  hashBlake3,
  digestBlake3,
  encodeBase58,
} from '../util/encoding.mjs';

const ajv = new Ajv({ allErrors: true, strict: false });

function isPlainObject(value) {
  if (!value || typeof value !== 'object') return false;
  if (Array.isArray(value)) return false;
  if (value instanceof Uint8Array) return false;
  if (Buffer.isBuffer?.(value)) return false;
  return true;
}

function ensureAjvSchema(schema) {
  if (!schema || typeof schema !== 'object') {
    throw new Error('jsonschema.validate requires a schema object');
  }
  const key = stableStringify(schema);
  if (!ajv.getSchema(key)) {
    ajv.addSchema(schema, key);
  }
  return ajv.getSchema(key);
}

function emptyDiff(diff) {
  return (
    Object.keys(diff.added).length === 0 &&
    Object.keys(diff.removed).length === 0 &&
    Object.keys(diff.changed).length === 0
  );
}

function stateDiff(base, target) {
  const result = {
    added: {},
    removed: {},
    changed: {},
  };

  if (!isPlainObject(base) || !isPlainObject(target)) {
    // Non-object inputs are treated as leaf states; differences surface as a root "" change entry.
    const equal = stableStringify(base) === stableStringify(target);
    if (!equal) {
      result.changed[''] = { from: base, to: target };
    }
    return result;
  }

  for (const key of Object.keys(target)) {
    if (!(key in base)) {
      result.added[key] = target[key];
    }
  }

  for (const key of Object.keys(base)) {
    if (!(key in target)) {
      result.removed[key] = base[key];
    }
  }

  for (const key of Object.keys(target)) {
    if (!(key in base)) continue;
    const left = base[key];
    const right = target[key];
    if (isPlainObject(left) && isPlainObject(right)) {
      const nested = stateDiff(left, right);
      if (!emptyDiff(nested)) {
        result.changed[key] = nested;
      }
      continue;
    }
    if (stableStringify(left) !== stableStringify(right)) {
      result.changed[key] = { from: left, to: right };
    }
  }

  return result;
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

function applyJsonPatch(base = {}, operations = []) {
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
      throw new Error('jsonpatch.apply: root operations are not supported');
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

function mergeGCounter(base = {}, patch = {}) {
  const result = {};
  const keys = new Set([...Object.keys(base || {}), ...Object.keys(patch || {})]);
  for (const key of keys) {
    const left = Number(base?.[key] ?? 0);
    const right = Number(patch?.[key] ?? 0);
    result[key] = Math.max(left, right);
  }
  const total = Object.values(result).reduce((sum, value) => sum + Number(value ?? 0), 0);
  return { counts: result, total };
}

function parseTimestampInput(value) {
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

function resolveIntervalMs(spec = {}) {
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

function alignTimestamp(timestampMs, intervalMs) {
  return Math.floor(timestampMs / intervalMs) * intervalMs;
}

function formatIso(epochMs) {
  return new Date(epochMs).toISOString();
}

function computeSagaId(steps = [], compensations = []) {
  const payload = stableStringify({ steps, compensations });
  return hashBlake3(payload);
}

export function runTransform(spec, input = {}) {
  if (!spec || typeof spec !== 'object') {
    throw new Error('spec must be an object');
  }
  const op = spec.op;
  switch (op) {
    case 'hash': {
      if (spec.alg !== 'blake3') {
        throw new Error(`Unsupported hash algorithm: ${spec.alg}`);
      }
      return hashBlake3(input);
    }
    case 'digest': {
      if (spec.alg !== 'blake3') {
        throw new Error(`Unsupported digest algorithm: ${spec.alg}`);
      }
      return digestBlake3(input);
    }
    case 'concat': {
      const parts = Array.isArray(input)
        ? input
        : Array.isArray(input?.parts)
          ? input.parts
          : Object.keys(input).sort().map((k) => input[k]);
      return parts.map((p) => (p == null ? '' : String(p))).join('');
    }
    case 'get': {
      const path = spec.path;
      if (typeof path !== 'string' || !path) {
        throw new Error('get requires a string path');
      }
      const segments = path.split('.');
      let current = input.value;
      for (const seg of segments) {
        if (current == null) return undefined;
        current = current[seg];
      }
      return current;
    }
    case 'jsonschema.validate': {
      if (typeof spec.schema === 'string') {
        // Keep transform pure: resolving string schema IDs would require IO; reject upfront.
        throw new Error('jsonschema.validate: string schema IDs are not supported in pure Transform; provide an inline object schema.');
      }
      const schema = spec.schema;
      const validator = ensureAjvSchema(schema);
      const valid = validator(input.value);
      if (!valid) {
        const errors = validator.errors?.map((e) => `${e.instancePath} ${e.message}`).join(', ');
        throw new Error(`Schema validation failed: ${errors}`);
      }
      return input.value;
    }
    case 'model_infer': {
      // Deterministic stub for CI stability (hash features into a stable bucket).
      const payload = stableStringify({ model: spec.model, features: input.features });
      const hashBytes = digestBlake3(payload);
      const score = Number(BigInt('0x' + Buffer.from(hashBytes.slice(0, 8)).toString('hex')) % BigInt(1000)) / 1000;
      const bucket = score > 0.66 ? 'high' : score > 0.33 ? 'medium' : 'low';
      return { score, bucket, model: spec.model };
    }
    case 'policy_eval': {
      // Deterministic stub for CI stability (no IO/time; hash input to a decision).
      const payload = stableStringify({ policy: spec.policy, input: input.input });
      const hashBytes = digestBlake3(payload);
      const decision = hashBytes[0] % 2 === 0 ? 'allow' : 'deny';
      const amount = Number(BigInt('0x' + Buffer.from(hashBytes.slice(1, 9)).toString('hex')) % BigInt(500000)) / 100;
      return { decision, amount, policy: spec.policy };
    }
    case 'encode_base58': {
      return encodeBase58(input.value);
    }
    case 'state_diff': {
      const base = input.base ?? {};
      const target = input.target ?? {};
      return stateDiff(base, target);
    }
    case 'jsonpatch.apply': {
      // Minimal JSON Patch implementation (objects only, add/replace/remove).
      const base = input.base ?? {};
      const patch = input.patch ?? input.operations ?? [];
      return applyJsonPatch(base, patch);
    }
    case 'crdt.gcounter.merge': {
      const base = input.base ?? {};
      const patch = input.patch ?? {};
      return mergeGCounter(base, patch);
    }
    case 'await.any': {
      const events = Array.isArray(input.events) ? input.events : [];
      for (let i = 0; i < events.length; i += 1) {
        const event = events[i];
        if (event !== undefined && event !== null) {
          return { index: i, event };
        }
      }
      return { index: -1, event: null };
    }
    case 'await.all': {
      const events = Array.isArray(input.events) ? input.events : [];
      return events.map((event) => (event === undefined ? null : event));
    }
    case 'time.parseTimestamp': {
      const epochMs = parseTimestampInput(input.value ?? input.timestamp ?? input.time);
      return { epoch_ms: epochMs, iso: formatIso(epochMs) };
    }
    case 'time.align': {
      const epochMs = parseTimestampInput(input.value ?? input.timestamp ?? input.time);
      const intervalMs = resolveIntervalMs(spec);
      const aligned = alignTimestamp(epochMs, intervalMs);
      return { epoch_ms: aligned, iso: formatIso(aligned), interval_ms: intervalMs };
    }
    case 'time.windowKey': {
      const epochMs = parseTimestampInput(input.value ?? input.timestamp ?? input.time);
      const intervalMs = resolveIntervalMs(spec);
      const start = alignTimestamp(epochMs, intervalMs);
      const end = start + intervalMs;
      return {
        start_ms: start,
        end_ms: end,
        key: `${formatIso(start)}/${formatIso(end)}`,
        interval_ms: intervalMs,
      };
    }
    case 'auth.sign': {
      const alg = spec.alg ?? 'blake3';
      const payload = stableStringify({ key: input.key, payload: input.payload, alg });
      const signature = hashBlake3(payload);
      return { signature, alg };
    }
    case 'auth.verify': {
      const alg = spec.alg ?? 'blake3';
      const payload = stableStringify({ key: input.key, payload: input.payload, alg });
      const expected = hashBlake3(payload);
      const provided = String(input.signature ?? '');
      return { valid: expected === provided, alg, expected, provided };
    }
    case 'auth.mint_token': {
      const alg = spec.alg ?? 'blake3';
      const payload = stableStringify({ secret: input.secret, claims: input.claims, alg });
      const digest = digestBlake3(payload);
      const token = `tok_${encodeBase58(digest)}`;
      return { token, claims: cloneValue(input.claims ?? {}), alg };
    }
    case 'auth.check_token': {
      const alg = spec.alg ?? 'blake3';
      const payload = stableStringify({ secret: input.secret, claims: input.claims, alg });
      const digest = digestBlake3(payload);
      const expected = `tok_${encodeBase58(digest)}`;
      const provided = String(input.token ?? '');
      return { valid: expected === provided, alg, expected, provided };
    }
    case 'process.saga.plan': {
      const steps = Array.isArray(input.steps) ? cloneValue(input.steps) : [];
      const compensations = Array.isArray(input.compensations) ? cloneValue(input.compensations) : [];
      const sagaId = computeSagaId(steps, compensations);
      return { saga_id: sagaId, steps, compensations };
    }
    default:
      throw new Error(`Unsupported transform op: ${op}`);
  }
}

export const ops = {
  runTransform,
};

