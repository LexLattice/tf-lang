import { createHash, createHmac, timingSafeEqual } from 'node:crypto';

const encoder = new TextEncoder();

function isHexString(value) {
  return typeof value === 'string' && value.length % 2 === 0 && /^[0-9a-f]+$/i.test(value);
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

function toUint8Array(value) {
  if (value instanceof Uint8Array) {
    return value;
  }
  if (ArrayBuffer.isView(value)) {
    return new Uint8Array(value.buffer, value.byteOffset, value.byteLength);
  }
  if (value instanceof ArrayBuffer) {
    return new Uint8Array(value);
  }
  if (typeof value === 'string') {
    if (isHexString(value)) {
      return new Uint8Array(Buffer.from(value, 'hex'));
    }
    return encoder.encode(value);
  }
  if (value === null || value === undefined) {
    return new Uint8Array(0);
  }
  if (typeof value === 'number') {
    return encoder.encode(String(value));
  }
  if (typeof value === 'boolean') {
    return encoder.encode(value ? 'true' : 'false');
  }
  return encoder.encode(stableStringify(value));
}

function normalizeString(value) {
  if (value === null || value === undefined) {
    return '';
  }
  if (typeof value === 'string') {
    return value;
  }
  if (typeof value === 'number' || typeof value === 'bigint' || typeof value === 'boolean') {
    return String(value);
  }
  if (value instanceof Uint8Array || ArrayBuffer.isView(value) || value instanceof ArrayBuffer) {
    return Buffer.from(toUint8Array(value)).toString('utf8');
  }
  return stableStringify(value);
}

function snapshotStorage(storage) {
  const out = new Map();
  for (const [uri, bucket] of storage.entries()) {
    out.set(uri, new Map(bucket.entries()));
  }
  return out;
}

export function createInmemAdapters(options = {}) {
  const published = [];
  const storage = new Map();
  const idempotency = new Set();
  const metrics = new Map();
  const keyMap = new Map(Object.entries(options.keys || { k1: 'secret' }));

  function bucketFor(uri) {
    if (!storage.has(uri)) {
      storage.set(uri, new Map());
    }
    return storage.get(uri);
  }

  function recordMetric(name, value) {
    const current = metrics.get(name) || 0;
    metrics.set(name, current + value);
  }

  async function publish(topic, key, payload) {
    const entry = {
      topic: normalizeString(topic),
      key: normalizeString(key),
      payload: normalizeString(payload),
    };
    published.push(entry);
  }

  async function writeObject(uri, key, value, idempotencyKey) {
    const targetUri = normalizeString(uri);
    const targetKey = normalizeString(key);
    const targetValue = normalizeString(value);
    if (idempotencyKey) {
      const token = `${targetUri}#${targetKey}#${normalizeString(idempotencyKey)}`;
      if (idempotency.has(token)) {
        return;
      }
      idempotency.add(token);
    }
    bucketFor(targetUri).set(targetKey, targetValue);
  }

  async function readObject(uri, key) {
    const targetUri = normalizeString(uri);
    const targetKey = normalizeString(key);
    const bucket = storage.get(targetUri);
    if (!bucket || !bucket.has(targetKey)) {
      return null;
    }
    return bucket.get(targetKey);
  }

  async function compareAndSwap(uri, key, expect, update) {
    const targetUri = normalizeString(uri);
    const targetKey = normalizeString(key);
    const bucket = storage.get(targetUri);
    if (!bucket || !bucket.has(targetKey)) {
      return false;
    }
    const current = bucket.get(targetKey);
    if (current !== normalizeString(expect)) {
      return false;
    }
    bucket.set(targetKey, normalizeString(update));
    return true;
  }

  function loadKey(keyId) {
    const secret = keyMap.get(keyId);
    if (typeof secret !== 'string') {
      throw new Error(`inmem adapters: unknown keyId ${keyId}`);
    }
    return secret;
  }

  async function sign(keyId, data) {
    const secret = loadKey(normalizeString(keyId));
    const bytes = toUint8Array(data);
    return createHmac('sha256', secret).update(bytes).digest();
  }

  async function verify(keyId, data, sig) {
    const secret = loadKey(normalizeString(keyId));
    const bytes = toUint8Array(data);
    const expected = createHmac('sha256', secret).update(bytes).digest();
    const actual = toUint8Array(sig);
    const actualBuffer = Buffer.from(actual);
    if (actualBuffer.length !== expected.length) {
      return false;
    }
    return timingSafeEqual(expected, actualBuffer);
  }

  async function hash(data) {
    const bytes = toUint8Array(data);
    const digest = createHash('sha256').update(bytes).digest('hex');
    return `sha256:${digest}`;
  }

  async function emitMetric(name, value = 1) {
    const metricName = normalizeString(name);
    const numeric = Number(value ?? 1);
    const delta = Number.isFinite(numeric) ? numeric : 1;
    recordMetric(metricName, delta);
  }

  function reset() {
    published.length = 0;
    storage.clear();
    idempotency.clear();
    metrics.clear();
  }

  return {
    adapters: {
      publish,
      writeObject,
      readObject,
      compareAndSwap,
      sign,
      verify,
      hash,
      emitMetric,
    },
    reset,
    getPublished() {
      return published.map((entry) => ({ ...entry }));
    },
    getStorageSnapshot() {
      return snapshotStorage(storage);
    },
    getMetrics() {
      return new Map(metrics.entries());
    },
  };
}

export default createInmemAdapters;
