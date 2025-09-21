import { createHash, createHmac } from 'node:crypto';

function ensureString(value) {
  return typeof value === 'string' ? value : String(value ?? '');
}

function asUint8Array(data) {
  if (data instanceof Uint8Array) {
    return data;
  }
  if (ArrayBuffer.isView(data)) {
    return new Uint8Array(data.buffer, data.byteOffset, data.byteLength);
  }
  if (Array.isArray(data)) {
    return Uint8Array.from(data);
  }
  if (typeof data === 'string') {
    return new TextEncoder().encode(data);
  }
  if (data instanceof ArrayBuffer) {
    return new Uint8Array(data);
  }
  throw new TypeError('Expected data to be convertible to Uint8Array');
}

export function createInmemAdapters(options = {}) {
  const published = [];
  const topics = new Map();
  const storage = new Map();
  const idempotencyTokens = new Set();
  const metricCounters = new Map();
  const keyMap = Object.assign({ k1: 'secret' }, options.keys || {});

  function storageBucket(uri) {
    if (!storage.has(uri)) {
      storage.set(uri, new Map());
    }
    return storage.get(uri);
  }

  const adapters = {
    async publish(topic, key, payload) {
      const entry = {
        topic: ensureString(topic),
        key: ensureString(key),
        payload: ensureString(payload),
      };
      published.push(entry);
      if (!topics.has(entry.topic)) {
        topics.set(entry.topic, []);
      }
      topics.get(entry.topic).push(entry);
    },

    async writeObject(uri, key, value, idempotencyKey) {
      const bucket = storageBucket(ensureString(uri));
      const storageKey = ensureString(key);
      const valueStr = ensureString(value);
      if (idempotencyKey) {
        const token = `${ensureString(uri)}#${storageKey}#${ensureString(idempotencyKey)}`;
        if (idempotencyTokens.has(token)) {
          return;
        }
        idempotencyTokens.add(token);
      }
      bucket.set(storageKey, valueStr);
    },

    async readObject(uri, key) {
      const bucket = storage.get(ensureString(uri));
      if (!bucket) return null;
      if (!bucket.has(ensureString(key))) return null;
      return bucket.get(ensureString(key));
    },

    async compareAndSwap(uri, key, expect, update) {
      const bucket = storage.get(ensureString(uri));
      if (!bucket) return false;
      const storageKey = ensureString(key);
      if (!bucket.has(storageKey)) return false;
      const current = bucket.get(storageKey);
      if (current !== ensureString(expect)) {
        return false;
      }
      bucket.set(storageKey, ensureString(update));
      return true;
    },

    async sign(keyId, data) {
      const key = keyMap[keyId];
      if (typeof key !== 'string') {
        throw new Error(`inmem adapters: unknown keyId ${keyId}`);
      }
      const payload = asUint8Array(data);
      const hmac = createHmac('sha256', key);
      hmac.update(payload);
      return Uint8Array.from(hmac.digest());
    },

    async verify(keyId, data, sig) {
      const key = keyMap[keyId];
      if (typeof key !== 'string') {
        return false;
      }
      const expected = await adapters.sign(keyId, data);
      const provided = asUint8Array(sig);
      if (expected.length !== provided.length) {
        return false;
      }
      let mismatch = 0;
      for (let i = 0; i < expected.length; i += 1) {
        mismatch |= expected[i] ^ provided[i];
      }
      return mismatch === 0;
    },

    async hash(data) {
      const payload = asUint8Array(data);
      const digest = createHash('sha256').update(payload).digest('hex');
      return digest;
    },

    async emitMetric(name, value = 1) {
      const metricName = ensureString(name);
      const delta = Number.isFinite(value) ? Number(value) : 1;
      const current = metricCounters.get(metricName) ?? 0;
      metricCounters.set(metricName, current + delta);
    },

    getPublished() {
      return published.map((entry) => ({ ...entry }));
    },

    getMetrics() {
      return new Map(metricCounters);
    },

    getTopics() {
      const out = new Map();
      for (const [topic, list] of topics.entries()) {
        out.set(topic, list.map((entry) => ({ ...entry })));
      }
      return out;
    },

    getStorageSnapshot() {
      const out = new Map();
      for (const [uri, bucket] of storage.entries()) {
        out.set(uri, new Map(bucket));
      }
      return out;
    },

    reset() {
      published.length = 0;
      topics.clear();
      storage.clear();
      idempotencyTokens.clear();
      metricCounters.clear();
    },
  };

  Object.defineProperty(adapters, 'state', {
    enumerable: false,
    value: {
      topics,
      storage,
      metrics: metricCounters,
    },
  });

  return adapters;
}

export default createInmemAdapters;
