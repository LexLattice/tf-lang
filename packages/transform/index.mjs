import Ajv from 'ajv';
import {
  stableStringify,
  hashBlake3,
  digestBlake3,
  encodeBase58,
} from '../util/encoding.mjs';
import {
  applyJsonPatch,
  mergeGCounter,
  parseTimestampInput,
  resolveIntervalMs,
  alignTimestamp,
  formatIso,
  computeSagaId,
  cloneDeep,
} from '../ops/xforms.mjs';
import { mintTokenDeterministic, checkTokenDeterministic } from '../ops/auth.mjs';

const ajv = new Ajv({ allErrors: true, strict: false });

const registry = new Map();
const deterministicOps = new Set();

function register(op, handler, options = {}) {
  if (typeof op !== 'string' || op.length === 0) {
    throw new Error('transform op must be a non-empty string');
  }
  if (typeof handler !== 'function') {
    throw new Error(`transform handler for ${op} must be a function`);
  }
  registry.set(op, handler);
  if (options.deterministic !== false) {
    deterministicOps.add(op);
  } else {
    deterministicOps.delete(op);
  }
  return () => {
    const current = registry.get(op);
    if (current === handler) {
      registry.delete(op);
      deterministicOps.delete(op);
    }
  };
}

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
    Object.keys(diff.added).length === 0
    && Object.keys(diff.removed).length === 0
    && Object.keys(diff.changed).length === 0
  );
}

function stateDiff(base, target) {
  const result = {
    added: {},
    removed: {},
    changed: {},
  };

  if (!isPlainObject(base) || !isPlainObject(target)) {
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

function registerBuiltin(op, handler, options) {
  register(op, handler, options);
}

registerBuiltin('hash', (spec, input) => {
  if (spec.alg && spec.alg !== 'blake3') {
    throw new Error(`Unsupported hash algorithm: ${spec.alg}`);
  }
  return hashBlake3(input);
});

registerBuiltin('digest', (spec, input) => {
  if (spec.alg && spec.alg !== 'blake3') {
    throw new Error(`Unsupported digest algorithm: ${spec.alg}`);
  }
  return digestBlake3(input);
});

registerBuiltin('concat', (spec, input) => {
  const parts = Array.isArray(input)
    ? input
    : Array.isArray(input?.parts)
      ? input.parts
      : Object.keys(input).sort().map((k) => input[k]);
  return parts.map((p) => (p == null ? '' : String(p))).join('');
});

registerBuiltin('eq', (spec, input) => {
  const left = input.left ?? input.a ?? input.first;
  const right = input.right ?? input.b ?? input.second;
  return left === right;
});

registerBuiltin('get', (spec, input) => {
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
});

registerBuiltin('jsonschema.validate', (spec, input) => {
  const schema = spec.schema;
  if (typeof schema === 'string') {
    throw new Error('jsonschema.validate: string schema IDs are not supported in pure Transform; provide an inline object schema.');
  }
  const validator = ensureAjvSchema(schema);
  const valid = validator(input.value);
  if (!valid) {
    const errors = validator.errors?.map((e) => `${e.instancePath} ${e.message}`).join(', ');
    throw new Error(`Schema validation failed: ${errors}`);
  }
  return input.value;
});

registerBuiltin('model_infer', (spec, input) => {
  const payload = stableStringify({ model: spec.model, features: input.features });
  const hashBytes = digestBlake3(payload);
  const score = Number(BigInt('0x' + Buffer.from(hashBytes.slice(0, 8)).toString('hex')) % BigInt(1000)) / 1000;
  const bucket = score > 0.66 ? 'high' : score > 0.33 ? 'medium' : 'low';
  return { score, bucket, model: spec.model };
});

registerBuiltin('policy_eval', (spec, input) => {
  const payload = stableStringify({ policy: spec.policy, input: input.input });
  const hashBytes = digestBlake3(payload);
  const decision = hashBytes[0] % 2 === 0 ? 'allow' : 'deny';
  const amount = Number(BigInt('0x' + Buffer.from(hashBytes.slice(1, 9)).toString('hex')) % BigInt(500000)) / 100;
  return { decision, amount, policy: spec.policy };
});

registerBuiltin('encode_base58', (spec, input) => encodeBase58(input.value));

registerBuiltin('state_diff', (spec, input) => {
  const base = input.base ?? {};
  const target = input.target ?? {};
  return stateDiff(base, target);
});

registerBuiltin('jsonpatch.apply', (spec, input) => {
  const base = input.base ?? {};
  const patch = input.patch ?? input.operations ?? [];
  return applyJsonPatch(base, patch);
});

registerBuiltin('crdt.gcounter.merge', (spec, input) => {
  const base = input.base ?? {};
  const patch = input.patch ?? {};
  return mergeGCounter(base, patch);
});

registerBuiltin('await.any', (spec, input) => {
  const events = Array.isArray(input.events) ? input.events : [];
  for (let i = 0; i < events.length; i += 1) {
    const event = events[i];
    if (event !== undefined && event !== null) {
      return { index: i, event };
    }
  }
  return { index: -1, event: null };
});

registerBuiltin('await.all', (spec, input) => {
  const events = Array.isArray(input.events) ? input.events : [];
  return events.map((event) => (event === undefined ? null : event));
});

registerBuiltin('time.parseTimestamp', (spec, input) => {
  const epochMs = parseTimestampInput(input.value ?? input.timestamp ?? input.time);
  return { epoch_ms: epochMs, iso: formatIso(epochMs) };
});

registerBuiltin('time.align', (spec, input) => {
  const epochMs = parseTimestampInput(input.value ?? input.timestamp ?? input.time);
  const intervalMs = resolveIntervalMs(spec);
  const aligned = alignTimestamp(epochMs, intervalMs);
  return { epoch_ms: aligned, iso: formatIso(aligned), interval_ms: intervalMs };
});

registerBuiltin('time.windowKey', (spec, input) => {
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
});

registerBuiltin('auth.sign', (spec, input) => {
  const alg = spec.alg ?? 'blake3';
  const payload = stableStringify({ key: input.key, payload: input.payload, alg });
  const signature = hashBlake3(payload);
  return { signature, alg };
});

registerBuiltin('auth.verify', (spec, input) => {
  const alg = spec.alg ?? 'blake3';
  const payload = stableStringify({ key: input.key, payload: input.payload, alg });
  const expected = hashBlake3(payload);
  const provided = String(input.signature ?? '');
  return { valid: expected === provided, alg, expected, provided };
});

registerBuiltin('auth.mint_token', (spec, input) => {
  const alg = spec.alg ?? 'blake3';
  return mintTokenDeterministic({ secret: input.secret, claims: input.claims, alg });
});

registerBuiltin('auth.check_token', (spec, input) => {
  const alg = spec.alg ?? 'blake3';
  const { token: expected } = mintTokenDeterministic({ secret: input.secret, claims: input.claims, alg });
  const provided = String(input.token ?? '');
  const valid = checkTokenDeterministic(provided, { secret: input.secret, claims: input.claims, alg });
  return { valid, alg, expected, provided };
});

registerBuiltin('process.saga.plan', (spec, input) => {
  const steps = Array.isArray(input.steps) ? cloneDeep(input.steps) : [];
  const compensations = Array.isArray(input.compensations) ? cloneDeep(input.compensations) : [];
  const sagaId = computeSagaId(steps, compensations);
  return { saga_id: sagaId, steps, compensations };
});

export function registerTransform(op, handler, options) {
  return register(op, handler, options);
}

export function getTransform(op) {
  return registry.get(op) ?? null;
}

export function listTransforms() {
  return [...registry.keys()].sort();
}

export function runTransform(spec, input = {}) {
  if (!spec || typeof spec !== 'object') {
    throw new Error('spec must be an object');
  }
  const op = spec.op;
  if (typeof op !== 'string' || op.length === 0) {
    throw new Error('transform spec missing op');
  }
  const handler = registry.get(op);
  if (!handler) {
    throw new Error(`Unsupported transform op: ${op}`);
  }
  return handler(spec, input);
}

export const DETERMINISTIC_TRANSFORMS = deterministicOps;

export const ops = {
  runTransform,
};

export default {
  runTransform,
  registerTransform,
  getTransform,
  listTransforms,
};
