import { createHash } from 'node:crypto';
import { blake3 } from '@noble/hashes/blake3.js';
import { deepClone } from '../util/clone.mjs';
import createMemoryBus from './bus.memory.mjs';

export const DETERMINISTIC_TRANSFORMS = new Set([
  'concat',
  'get',
  'eq',
  'jsonschema.validate',
  'hash',
  'digest',
  'encode_base58',
  'model_infer',
  'policy_eval',
]);

export function stableStringify(value) {
  if (value === null || typeof value !== 'object') {
    return JSON.stringify(value);
  }
  if (Array.isArray(value)) {
    return `[${value.map((item) => stableStringify(item)).join(',')}]`;
  }
  const entries = Object.keys(value)
    .sort()
    .map((key) => `${JSON.stringify(key)}:${stableStringify(value[key])}`);
  return `{${entries.join(',')}}`;
}

function toBuffer(value) {
  if (Buffer.isBuffer(value)) {
    return value;
  }
  if (value instanceof Uint8Array) {
    return Buffer.from(value);
  }
  if (typeof value === 'string') {
    return Buffer.from(value, 'utf8');
  }
  return Buffer.from(stableStringify(value), 'utf8');
}

export function hashPayload(payload, { alg = 'blake3' } = {}) {
  const data = toBuffer(payload);
  if (alg === 'blake3') {
    const digest = blake3(data);
    return Buffer.from(digest).toString('hex');
  }
  if (alg === 'sha256' || alg === 'sha512') {
    return createHash(alg).update(data).digest('hex');
  }
  throw new Error(`unsupported hash algorithm: ${alg}`);
}

function pathLookup(source, path) {
  if (!path) {
    return undefined;
  }
  const parts = path.split('.');
  let current = source;
  for (const part of parts) {
    if (current === null || current === undefined) {
      return undefined;
    }
    if (!Object.prototype.hasOwnProperty.call(current, part)) {
      return undefined;
    }
    current = current[part];
  }
  return current;
}

function resolveReference(ref, context) {
  if (typeof ref !== 'string' || !ref.startsWith('@')) {
    return ref;
  }
  const path = ref.slice(1);
  if (path.length === 0) {
    return undefined;
  }
  const [head, ...rest] = path.split('.');
  const base = context[head];
  if (rest.length === 0) {
    return base;
  }
  return pathLookup(base, rest.join('.'));
}

function resolveTemplate(template, context) {
  if (typeof template === 'string') {
    return resolveReference(template, context);
  }
  if (Array.isArray(template)) {
    return template.map((item) => resolveTemplate(item, context));
  }
  if (template && typeof template === 'object') {
    const out = {};
    for (const [key, value] of Object.entries(template)) {
      out[key] = resolveTemplate(value, context);
    }
    return out;
  }
  return template;
}

function evaluateWhen(condition, context) {
  if (condition === undefined || condition === null) {
    return true;
  }
  if (typeof condition === 'string') {
    return Boolean(resolveTemplate(condition, context));
  }
  if (typeof condition !== 'object') {
    return Boolean(condition);
  }
  const { op } = condition;
  switch (op) {
    case 'not':
      return !evaluateWhen(condition.value ?? condition.arg ?? condition.operand, context);
    case 'and': {
      const terms = Array.isArray(condition.args)
        ? condition.args
        : [condition.left, condition.right].filter((value) => value !== undefined);
      return terms.every((term) => evaluateWhen(term, context));
    }
    case 'or': {
      const terms = Array.isArray(condition.args)
        ? condition.args
        : [condition.left, condition.right].filter((value) => value !== undefined);
      return terms.some((term) => evaluateWhen(term, context));
    }
    case 'eq': {
      const left = resolveTemplate(condition.left ?? condition.a, context);
      const right = resolveTemplate(condition.right ?? condition.b, context);
      return left === right;
    }
    default:
      return Boolean(resolveTemplate(condition, context));
  }
}

function encodeBase58(value) {
  const alphabet = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';
  const input = Buffer.from(String(value ?? ''), 'utf8');
  if (input.length === 0) {
    return '';
  }
  let zeros = 0;
  for (const byte of input) {
    if (byte === 0) {
      zeros += 1;
    } else {
      break;
    }
  }
  let num = BigInt(`0x${input.toString('hex')}`);
  let encoded = '';
  while (num > 0n) {
    const rem = Number(num % 58n);
    encoded = alphabet[rem] + encoded;
    num /= 58n;
  }
  return '1'.repeat(zeros) + encoded;
}

function makeKeypair(node) {
  const algorithm = node.algorithm ?? 'Keypair';
  const label = node.id ?? algorithm;
  const seed = Buffer.from(`${algorithm}:${label}`).toString('base64');
  return {
    algorithm,
    public_key_pem: `-----BEGIN ${algorithm} PUBLIC KEY-----\n${seed}\n-----END ${algorithm} PUBLIC KEY-----`,
    private_key_pem: `-----BEGIN ${algorithm} PRIVATE KEY-----\n${seed}\n-----END ${algorithm} PRIVATE KEY-----`,
    capability: `cap:keypair:${algorithm.toLowerCase()}`,
  };
}

function computeModelInference(input) {
  const serialized = stableStringify(input);
  const digest = hashPayload(serialized, { alg: 'blake3' });
  const slice = digest.slice(0, 8);
  const numeric = parseInt(slice, 16);
  const score = (numeric % 1000) / 1000;
  return {
    score,
    label: score > 0.5 ? 'high' : 'low',
  };
}

function evaluateTransform(node, context) {
  const spec = node.spec ?? {};
  const op = spec.op ?? 'identity';
  const input = {};
  if (node.in && typeof node.in === 'object') {
    for (const [key, value] of Object.entries(node.in)) {
      input[key] = resolveTemplate(value, context);
    }
  }
  switch (op) {
    case 'concat':
      return Object.values(input)
        .map((value) => (value === null || value === undefined ? '' : String(value)))
        .join('');
    case 'get':
      return pathLookup(input.value ?? input.source ?? input.obj ?? input.from, spec.path ?? spec.key ?? '');
    case 'eq':
      return input.a === input.b || input.left === input.right;
    case 'jsonschema.validate':
      return { valid: true, value: input.value ?? input.data ?? null, errors: [] };
    case 'hash':
      return hashPayload(input, { alg: spec.alg ?? 'blake3' });
    case 'digest': {
      const alg = spec.alg ?? 'blake3';
      const hex = hashPayload(input, { alg });
      return `${alg}:${hex}`;
    }
    case 'encode_base58':
      return encodeBase58(input.value ?? input.text ?? '');
    case 'model_infer':
      return computeModelInference(input);
    case 'policy_eval':
      return {
        allowed: true,
        reason: 'stub-allow',
        input,
      };
    default:
      throw new Error(`unsupported transform op: ${op}`);
  }
}

function collectHandlerPatterns(handlers = {}) {
  return Object.entries(handlers).map(([pattern, fn]) => {
    if (typeof fn !== 'function') {
      throw new Error(`handler for ${pattern} must be a function`);
    }
    const normalized = pattern.replace(/[.*+?^${}()|[\]\\]/g, '\\$&').replace(/\\\*/g, '.*');
    return { regex: new RegExp(`^${normalized}$`), fn };
  });
}

export async function executeL0(l0, options = {}) {
  if (!l0 || !Array.isArray(l0.nodes)) {
    throw new Error('executeL0 requires an L0 pipeline with nodes');
  }
  const bus = options.bus ?? createMemoryBus();
  const timeout = typeof options.timeout === 'number' ? options.timeout : 50;
  const trace = {
    publishes: [],
    subscribes: [],
    transforms: [],
    keypairs: [],
  };
  const context = {};

  if (Array.isArray(options.seed)) {
    for (const entry of options.seed) {
      if (!entry || typeof entry.topic !== 'string') {
        continue;
      }
      await bus.publish(entry.topic, deepClone(entry.message ?? {}), {
        meta: { seed: true, ...(entry.meta ?? {}) },
      });
    }
  }

  const handlerPatterns = collectHandlerPatterns(options.handlers ?? {});

  for (const node of l0.nodes) {
    if (!['Transform', 'Publish', 'Subscribe', 'Keypair'].includes(node.kind)) {
      throw new Error(`unsupported node kind: ${node.kind}`);
    }
    if (!evaluateWhen(node.when, context)) {
      continue;
    }
    if (node.kind === 'Transform') {
      const result = evaluateTransform(node, context);
      if (node.out?.var) {
        context[node.out.var] = result;
      }
      trace.transforms.push({ id: node.id, op: node.spec?.op, result });
      continue;
    }
    if (node.kind === 'Keypair') {
      const keypair = makeKeypair(node);
      if (node.out?.var) {
        context[node.out.var] = keypair;
      }
      trace.keypairs.push({ id: node.id, algorithm: keypair.algorithm });
      continue;
    }
    if (node.kind === 'Subscribe') {
      const channel = resolveTemplate(node.channel, context);
      const filter = resolveTemplate(node.filter, context);
      const entry = await bus.receive(channel, { filter, timeout });
      if (node.out?.var) {
        context[node.out.var] = entry.message;
      }
      trace.subscribes.push({ id: node.id, channel: entry.topic, message: entry.message, meta: entry.meta });
      continue;
    }
    if (node.kind === 'Publish') {
      const channel = resolveTemplate(node.channel, context);
      const payload = resolveTemplate(node.payload, context);
      await bus.publish(channel, payload, {
        qos: node.qos,
        meta: { nodeId: node.id },
        duplicates: node.duplicates,
      });
      trace.publishes.push({ id: node.id, channel, payload });
      for (const handler of handlerPatterns) {
        if (handler.regex.test(channel)) {
          await handler.fn({ channel, message: payload, node }, bus);
        }
      }
      continue;
    }
  }

  return { context, trace, bus };
}

export default executeL0;
