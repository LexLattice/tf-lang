import { createHash } from 'node:crypto';
import { createInmemAdapters } from '../adapters/inmem.mjs';

function stableStringify(value) {
  return JSON.stringify(canonicalize(value));
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

function encodeString(value) {
  return Buffer.from(value ?? '', 'utf8');
}

function encodeValue(value) {
  if (value instanceof Uint8Array) {
    return value;
  }
  if (Buffer.isBuffer(value)) {
    return value;
  }
  if (typeof value === 'string') {
    return encodeString(value);
  }
  return encodeString(JSON.stringify(value));
}

function decodeSignature(value) {
  if (value instanceof Uint8Array || Buffer.isBuffer(value)) {
    return value;
  }
  if (typeof value === 'string') {
    if (value.length === 0) {
      return encodeString('');
    }
    try {
      const buf = Buffer.from(value, 'base64');
      if (buf.length > 0 || value === '') {
        return buf;
      }
    } catch {
      // ignore and fall through
    }
    return encodeString(value);
  }
  return encodeValue(value);
}

function register(registry, handlers, canonicalId, aliases, effect, impl) {
  const entry = { canonicalId, effect, impl };
  const names = new Set([canonicalId, ...(aliases || [])]);
  for (const name of names) {
    registry.set(name, entry);
    handlers[name] = impl;
  }
}

export function createRuntimeFromAdapters(adapters = createInmemAdapters()) {
  const typed = adapters;
  const registry = new Map();
  const handlers = Object.create(null);

  register(
    registry,
    handlers,
    'tf:resource/write-object@1',
    ['write-object'],
    'Storage.Write',
    async ({ uri, key, value, idempotency_key }) => {
      await typed.writeObject?.(uri, key, value, idempotency_key);
      return { ok: true };
    },
  );

  register(
    registry,
    handlers,
    'tf:resource/read-object@1',
    ['read-object'],
    'Storage.Read',
    async ({ uri, key }) => {
      if (typeof typed.readObject !== 'function') {
        return { ok: false, value: null };
      }
      const value = await typed.readObject(uri, key);
      return { ok: value !== null && value !== undefined, value, etag: null };
    },
  );

  register(
    registry,
    handlers,
    'tf:resource/compare-and-swap@1',
    ['compare-and-swap'],
    'Storage.Write',
    async ({ uri, key, value, ifMatch, expect }) => {
      const expected = expect ?? ifMatch ?? '';
      const update = value ?? '';
      const ok = typeof typed.compareAndSwap === 'function'
        ? await typed.compareAndSwap(uri, key, expected, update)
        : false;
      return { ok, etag: null };
    },
  );

  register(
    registry,
    handlers,
    'tf:observability/emit-metric@1',
    ['emit-metric'],
    'Observability.EmitMetric',
    async ({ name, value }) => {
      await typed.emitMetric?.(name, value);
      return { ok: true };
    },
  );

  register(
    registry,
    handlers,
    'tf:network/publish@1',
    ['publish'],
    'Network.Out',
    async ({ topic, key, payload }) => {
      await typed.publish?.(topic ?? 'default', key ?? '', payload ?? '');
      return { ok: true };
    },
  );

  register(
    registry,
    handlers,
    'tf:information/hash@1',
    ['hash'],
    'Information.Hash',
    async (args = {}) => {
      const target = Object.prototype.hasOwnProperty.call(args, 'value') ? args.value : args;
      const canonical = stableStringify(target);
      const data = encodeString(canonical);
      let digest = null;
      if (typeof typed.hash === 'function') {
        digest = await typed.hash(data);
      } else {
        digest = createHash('sha256').update(data).digest('hex');
      }
      return { ok: true, hash: `sha256:${digest}` };
    },
  );

  register(
    registry,
    handlers,
    'tf:security/sign-data@1',
    ['sign-data'],
    'Crypto',
    async ({ key_ref, key, data, payload }) => {
      const keyId = key_ref ?? key ?? 'k1';
      const raw = payload ?? data ?? '';
      const bytes = encodeValue(raw);
      if (typeof typed.sign !== 'function') {
        throw new Error('inmem: sign adapter not available');
      }
      const sig = await typed.sign(keyId, bytes);
      return { ok: true, signature: Buffer.from(sig).toString('base64') };
    },
  );

  register(
    registry,
    handlers,
    'tf:security/verify-signature@1',
    ['verify-signature'],
    'Crypto',
    async ({ key_ref, key, data, payload, signature, sig }) => {
      const keyId = key_ref ?? key ?? 'k1';
      const raw = payload ?? data ?? '';
      const bytes = encodeValue(raw);
      const signed = signature ?? sig ?? '';
      if (typeof typed.verify !== 'function') {
        return { ok: false };
      }
      const provided = decodeSignature(signed);
      const ok = await typed.verify(keyId, bytes, provided);
      return { ok };
    },
  );

  function effectFor(name) {
    const entry = registry.get(name);
    return entry?.effect ?? null;
  }

  const runtime = handlers;

  runtime.getAdapter = function getAdapter(name) {
    return registry.get(name)?.impl ?? null;
  };

  runtime.canonicalPrim = function canonicalPrim(name) {
    return registry.get(name)?.canonicalId ?? name;
  };

  runtime.effectFor = effectFor;

  runtime.state = typed.state;

  runtime.reset = function reset() {
    if (typeof typed.reset === 'function') {
      typed.reset();
    }
  };

  runtime.adapters = typed;

  return runtime;
}

const defaultRuntime = createRuntimeFromAdapters();

export default defaultRuntime;
