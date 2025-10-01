import { createHash } from 'node:crypto';
import { blake3 } from '@noble/hashes/blake3.js';
import { stableStringify, encodeBase58 } from '../util/encoding.mjs';
import { deepClone } from '../util/clone.mjs';
import {
  applyJsonPatch,
  mergeGCounter,
  parseTimestampInput,
  resolveIntervalMs,
  alignTimestamp,
  formatIso,
  computeSagaId,
} from '../ops/xforms.mjs';
import { mintTokenDeterministic, checkTokenDeterministic } from '../ops/auth.mjs';
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
  'state_diff',
  'jsonpatch.apply',
  'crdt.gcounter.merge',
  'await.any',
  'await.all',
  'time.parseTimestamp',
  'time.align',
  'time.windowKey',
  'auth.sign',
  'auth.verify',
  'auth.mint_token',
  'auth.check_token',
  'process.saga.plan',
]);

export { stableStringify };

function isPlainObject(value) {
  if (!value || typeof value !== 'object') return false;
  if (Array.isArray(value)) return false;
  if (value instanceof Uint8Array) return false;
  if (Buffer.isBuffer(value)) return false;
  return true;
}

function stateDiff(base, target) {
  const result = { added: {}, removed: {}, changed: {} };
  if (!isPlainObject(base) || !isPlainObject(target)) {
    // Non-object inputs are treated as leaf states; differences surface as a root "" change entry.
    if (stableStringify(base) !== stableStringify(target)) {
      result.changed[''] = { from: base, to: target };
    }
    return result;
  }
  for (const key of Object.keys(target)) {
    if (!(key in base)) {
      result.added[key] = deepClone(target[key]);
    }
  }
  for (const key of Object.keys(base)) {
    if (!(key in target)) {
      result.removed[key] = deepClone(base[key]);
    }
  }
  for (const key of Object.keys(target)) {
    if (!(key in base)) continue;
    const left = base[key];
    const right = target[key];
    if (isPlainObject(left) && isPlainObject(right)) {
      const nested = stateDiff(left, right);
      if (
        Object.keys(nested.added).length
        || Object.keys(nested.removed).length
        || Object.keys(nested.changed).length
      ) {
        result.changed[key] = nested;
      }
      continue;
    }
    if (stableStringify(left) !== stableStringify(right)) {
      result.changed[key] = { from: deepClone(left), to: deepClone(right) };
    }
  }
  return result;
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
    case 'state_diff':
      return stateDiff(input.base ?? {}, input.target ?? {});
    case 'jsonpatch.apply':
      return applyJsonPatch(input.base ?? {}, input.patch ?? input.operations ?? []);
    case 'crdt.gcounter.merge':
      return mergeGCounter(input.base ?? {}, input.patch ?? {});
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
    case 'await.all':
      return (Array.isArray(input.events) ? input.events : []).map((event) => (event === undefined ? null : event));
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
      return { signature: hashPayload(payload, { alg }), alg };
    }
    case 'auth.verify': {
      const alg = spec.alg ?? 'blake3';
      const payload = stableStringify({ key: input.key, payload: input.payload, alg });
      const expected = hashPayload(payload, { alg });
      const provided = String(input.signature ?? '');
      return { valid: expected === provided, expected, provided, alg };
    }
    case 'auth.mint_token': {
      const alg = spec.alg ?? 'blake3';
      return mintTokenDeterministic({ secret: input.secret, claims: input.claims, alg });
    }
    case 'auth.check_token': {
      const alg = spec.alg ?? 'blake3';
      const { token: expected } = mintTokenDeterministic({ secret: input.secret, claims: input.claims, alg });
      const provided = String(input.token ?? '');
      const valid = checkTokenDeterministic(provided, { secret: input.secret, claims: input.claims, alg });
      return { valid, expected, provided, alg };
    }
    case 'process.saga.plan': {
      const steps = Array.isArray(input.steps) ? deepClone(input.steps) : [];
      const compensations = Array.isArray(input.compensations) ? deepClone(input.compensations) : [];
      const sagaId = computeSagaId(steps, compensations);
      return { saga_id: sagaId, steps, compensations };
    }
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
