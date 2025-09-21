import { createHash } from 'node:crypto';
import { assertAllowed } from './capabilities.mjs';
import { createInmemAdapters } from '../adapters/inmem.mjs';

function must(name, fn) {
  if (typeof fn !== 'function') {
    throw new Error(`adapter missing: ${name}`);
  }
  return fn;
}

function toBytes(value) {
  if (value instanceof Uint8Array) {
    return value;
  }
  if (typeof value === 'string') {
    return Buffer.from(value);
  }
  return Buffer.from(String(value ?? ''));
}

function canonicalize(value) {
  if (value === null || typeof value !== 'object') {
    return value;
  }
  if (Array.isArray(value)) {
    return value.map((item) => canonicalize(item));
  }
  const out = {};
  for (const key of Object.keys(value).sort()) {
    const canonical = canonicalize(value[key]);
    if (canonical !== undefined) {
      out[key] = canonical;
    }
  }
  return out;
}

function stableStringify(value) {
  return JSON.stringify(canonicalize(value));
}

const PRIMITIVES = [
  {
    id: 'tf:network/publish@1',
    aliases: ['publish'],
    effect: 'Network.Out',
    async invoke(adapters, args = {}, state) {
      const topic = typeof args.topic === 'string' ? args.topic : String(args.topic ?? '');
      const key = typeof args.key === 'string' ? args.key : String(args.key ?? '');
      const payload = typeof args.payload === 'string' ? args.payload : JSON.stringify(args.payload ?? '');
      await must('publish', adapters.publish)(topic, key, payload);
      if (state.topics) {
        if (!state.topics.has(topic)) {
          state.topics.set(topic, []);
        }
        state.topics.get(topic).push({ topic, key, payload });
      }
      return { ok: true };
    },
  },
  {
    id: 'tf:observability/emit-metric@1',
    aliases: ['emit-metric'],
    effect: 'Observability',
    async invoke(adapters, args = {}, state) {
      const value = Object.prototype.hasOwnProperty.call(args, 'value') ? args.value : undefined;
      await must('emitMetric', adapters.emitMetric)(
        String(args.name ?? ''),
        typeof value === 'number' ? value : undefined,
      );
      if (state.metricsLog) {
        state.metricsLog.push({ name: String(args.name ?? ''), value: typeof value === 'number' ? value : undefined });
      }
      return { ok: true };
    },
  },
  {
    id: 'tf:resource/write-object@1',
    aliases: ['write-object'],
    effect: 'Storage.Write',
    async invoke(adapters, args = {}) {
      const uri = String(args.uri ?? '');
      const key = String(args.key ?? '');
      const value = typeof args.value === 'string' ? args.value : JSON.stringify(args.value ?? '');
      const idempotencyKey = args.idempotency_key ?? args.idempotencyKey;
      await must('writeObject', adapters.writeObject)(
        uri,
        key,
        value,
        typeof idempotencyKey === 'string' ? idempotencyKey : undefined,
      );
      return { ok: true };
    },
  },
  {
    id: 'tf:resource/read-object@1',
    aliases: ['read-object'],
    effect: 'Storage.Read',
    async invoke(adapters, args = {}) {
      if (typeof adapters.readObject !== 'function') {
        return { ok: false, value: null };
      }
      const uri = String(args.uri ?? '');
      const key = String(args.key ?? '');
      const value = await adapters.readObject(uri, key);
      if (value === null || value === undefined) {
        return { ok: false, value: null };
      }
      return { ok: true, value };
    },
  },
  {
    id: 'tf:resource/compare-and-swap@1',
    aliases: ['compare-and-swap'],
    effect: 'Storage.Write',
    async invoke(adapters, args = {}) {
      if (typeof adapters.compareAndSwap !== 'function') {
        return { ok: false };
      }
      const uri = String(args.uri ?? '');
      const key = String(args.key ?? '');
      const expect = Object.prototype.hasOwnProperty.call(args, 'expect')
        ? args.expect
        : Object.prototype.hasOwnProperty.call(args, 'ifMatch')
          ? args.ifMatch
          : Object.prototype.hasOwnProperty.call(args, 'if_match')
            ? args.if_match
            : null;
      const update = Object.prototype.hasOwnProperty.call(args, 'value') ? args.value : args.update;
      const expectStr = expect === null || expect === undefined ? null : String(expect);
      const updateStr = update === null || update === undefined ? '' : String(update);
      const ok = await adapters.compareAndSwap(uri, key, expectStr, updateStr);
      return { ok };
    },
  },
  {
    id: 'tf:security/sign-data@1',
    aliases: ['sign-data'],
    effect: 'Crypto',
    async invoke(adapters, args = {}) {
      const keyId = String(args.key ?? args.key_ref ?? args.keyId ?? '');
      const payload = Object.prototype.hasOwnProperty.call(args, 'payload') ? args.payload : args.value;
      const data = toBytes(payload);
      const sig = await must('sign', adapters.sign)(keyId, data);
      return { ok: true, signature: sig };
    },
  },
  {
    id: 'tf:security/verify-signature@1',
    aliases: ['verify-signature'],
    effect: 'Crypto',
    async invoke(adapters, args = {}) {
      const keyId = String(args.key ?? args.key_ref ?? args.keyId ?? '');
      const payload = Object.prototype.hasOwnProperty.call(args, 'payload') ? args.payload : args.value;
      const signature = Object.prototype.hasOwnProperty.call(args, 'signature') ? args.signature : args.sig;
      const data = toBytes(payload);
      const sig = signature instanceof Uint8Array
        ? signature
        : Buffer.from(String(signature ?? ''), 'base64');
      const ok = await must('verify', adapters.verify)(keyId, data, sig);
      if (!ok) {
        throw new Error('signature verification failed');
      }
      return { ok: true };
    },
  },
  {
    id: 'tf:information/hash@1',
    aliases: ['hash'],
    effect: 'Crypto',
    async invoke(adapters, args = {}) {
      const target = Object.prototype.hasOwnProperty.call(args, 'value') ? args.value : args;
      const serialized = stableStringify(target);
      const adapterDigest = await must('hash', adapters.hash)(Buffer.from(serialized));
      const digest = typeof adapterDigest === 'string' && adapterDigest.length > 0
        ? adapterDigest
        : createHash('sha256').update(serialized).digest('hex');
      return { ok: true, hash: digest.startsWith('sha256:') ? digest : `sha256:${digest}` };
    },
  },
];

function buildRuntimeFromAdapters(adapters) {
  const registry = new Map();
  const adaptersTable = {};
  const state = {
    adapters,
    metricsLog: [],
    topics: new Map(),
    caps: null,
  };

  const wrap = (effectFamily, fn) =>
    async (args = {}, ctx) => {
      const context = ctx ?? state;
      assertAllowed(effectFamily, args, context?.caps);
      return fn(args, context);
    };

  for (const entry of PRIMITIVES) {
    const handler = wrap(entry.effect, async (args = {}, ctx = state) => entry.invoke(adapters, args, ctx ?? state));
    registry.set(entry.id, { canonical: entry.id, effect: entry.effect, handler });
    adaptersTable[entry.id] = handler;
    for (const alias of entry.aliases ?? []) {
      registry.set(alias, { canonical: entry.id, effect: entry.effect, handler });
      adaptersTable[alias] = handler;
    }
  }

  const runtime = {};

  runtime.getAdapter = (name) => registry.get(name)?.handler ?? null;
  runtime.canonicalPrim = (name) => registry.get(name)?.canonical ?? name;
  runtime.effectFor = (name) => registry.get(name)?.effect ?? null;
  runtime.adapters = adaptersTable;
  runtime.state = state;
  runtime.reset = () => {
    if (typeof adapters.reset === 'function') {
      adapters.reset();
    }
    state.metricsLog.length = 0;
    state.topics.clear();
  };
  if (typeof adapters.getPublished === 'function') {
    runtime.getPublished = adapters.getPublished;
  }
  if (typeof adapters.getStorageSnapshot === 'function') {
    runtime.getStorageSnapshot = adapters.getStorageSnapshot;
  }
  if (typeof adapters.getMetricTotals === 'function') {
    runtime.getMetricTotals = adapters.getMetricTotals;
  }

  for (const name of registry.keys()) {
    runtime[name] = registry.get(name)?.handler;
  }

  return runtime;
}

export function createInmemRuntime(options = {}) {
  const baseAdapters = options?.adapters ?? createInmemAdapters(options);
  return buildRuntimeFromAdapters(baseAdapters);
}

const defaultRuntime = createInmemRuntime();

export default defaultRuntime;
