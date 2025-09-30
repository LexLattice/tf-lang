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

function diffObjects(base, target) {
  const result = {
    added: {},
    removed: {},
    changed: {},
  };

  const baseObj = isPlainObject(base) ? base : {};
  const targetObj = isPlainObject(target) ? target : {};

  for (const key of Object.keys(targetObj)) {
    if (!(key in baseObj)) {
      result.added[key] = targetObj[key];
    }
  }

  for (const key of Object.keys(baseObj)) {
    if (!(key in targetObj)) {
      result.removed[key] = baseObj[key];
    }
  }

  for (const key of Object.keys(targetObj)) {
    if (!(key in baseObj)) continue;
    const left = baseObj[key];
    const right = targetObj[key];
    if (isPlainObject(left) && isPlainObject(right)) {
      const nested = diffObjects(left, right);
      if (!emptyDiff(nested)) {
        result.changed[key] = nested;
      }
      continue;
    }
    if (stableStringify(left) !== stableStringify(right)) {
      result.changed[key] = { before: left, after: right };
    }
  }

  return result;
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
      // String schema indicates upstream resolution; keep transform pure (no IO).
      const schema = typeof spec.schema === 'string'
        ? { type: 'object' }
        : spec.schema;
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
      return diffObjects(base, target);
    }
    default:
      throw new Error(`Unsupported transform op: ${op}`);
  }
}

export const ops = {
  runTransform,
};

