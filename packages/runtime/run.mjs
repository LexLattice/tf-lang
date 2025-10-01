import { createHash } from 'node:crypto';
import { blake3 } from '@noble/hashes/blake3.js';
import { stableStringify } from '../util/encoding.mjs';
import { deepClone } from '../util/clone.mjs';
import { runTransform, DETERMINISTIC_TRANSFORMS } from '../transform/index.mjs';
import createMemoryBus from './bus.memory.mjs';

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

function evaluateTransform(node, context) {
  const spec = node.spec ?? {};
  let input;
  if (Array.isArray(node.in)) {
    input = node.in.map((value) => resolveTemplate(value, context));
  } else if (node.in && typeof node.in === 'object') {
    input = {};
    for (const [key, value] of Object.entries(node.in)) {
      input[key] = resolveTemplate(value, context);
    }
  } else {
    input = {};
  }
  return runTransform(spec, input);
}

function recordVariableBinding(trace, context, node, value) {
  const varName = node?.out?.var;
  if (typeof varName !== 'string' || varName.length === 0) {
    return;
  }
  context[varName] = value;
  trace.variables.push({
    var: varName,
    node: node?.id ?? null,
    kind: node?.kind ?? null,
    op: node?.spec?.op ?? null,
    value: deepClone(value),
  });
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
  const ignoreTimeouts = options.ignoreTimeouts === true;
  const trace = {
    publishes: [],
    subscribes: [],
    transforms: [],
    keypairs: [],
    variables: [],
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
      recordVariableBinding(trace, context, node, result);
      const deterministic = node.spec?.op ? DETERMINISTIC_TRANSFORMS.has(node.spec.op) : null;
      trace.transforms.push({
        id: node.id,
        op: node.spec?.op,
        outVar: node.out?.var ?? null,
        result,
        deterministic,
      });
      continue;
    }
    if (node.kind === 'Keypair') {
      const keypair = makeKeypair(node);
      recordVariableBinding(trace, context, node, keypair);
      trace.keypairs.push({ id: node.id, algorithm: keypair.algorithm, outVar: node.out?.var ?? null });
      continue;
    }
    if (node.kind === 'Subscribe') {
      const channel = resolveTemplate(node.channel, context);
      const filter = resolveTemplate(node.filter, context);
      try {
        const entry = await bus.receive(channel, { filter, timeout });
        recordVariableBinding(trace, context, node, entry.message);
        trace.subscribes.push({ id: node.id, channel: entry.topic, message: entry.message, meta: entry.meta, outVar: node.out?.var ?? null });
      } catch (error) {
        if (!ignoreTimeouts || !(error?.message || '').startsWith('timeout waiting for channel')) {
          throw error;
        }
        recordVariableBinding(trace, context, node, null);
        trace.subscribes.push({ id: node.id, channel, error: error.message, outVar: node.out?.var ?? null });
      }
      continue;
    }
    if (node.kind === 'Publish') {
      const channel = resolveTemplate(node.channel, context);
      const payload = resolveTemplate(node.payload, context);
      if (ignoreTimeouts && (channel === null || channel === undefined || channel === '')) {
        trace.publishes.push({ id: node.id, channel: channel ?? null, payload, error: 'missing channel' });
        continue;
      }
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
