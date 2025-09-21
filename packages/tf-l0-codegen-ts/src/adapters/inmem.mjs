import { createHash, createHmac, timingSafeEqual } from 'node:crypto';

const DEFAULT_KEYS = { k1: 'secret' };

function toBuffer(value) {
  if (value instanceof Uint8Array) {
    return Buffer.from(value);
  }
  if (ArrayBuffer.isView(value)) {
    return Buffer.from(value.buffer, value.byteOffset, value.byteLength);
  }
  if (value instanceof ArrayBuffer) {
    return Buffer.from(value);
  }
  return Buffer.from(value ?? []);
}

function clonePublished(entry) {
  return { topic: entry.topic, key: entry.key, payload: entry.payload };
}

export function createInmemAdapters(options = {}) {
  const keyEntries = Object.entries(options?.keys ?? {});
  const keys = keyEntries.length > 0 ? keyEntries : Object.entries(DEFAULT_KEYS);
  const keyMap = new Map(keys);

  const published = [];
  const storage = new Map();
  const idempotencyTokens = new Set();
  const metrics = new Map();

  function ensureBucket(uri) {
    if (!storage.has(uri)) {
      storage.set(uri, new Map());
    }
    return storage.get(uri);
  }

  function readBucket(uri) {
    return storage.get(uri) ?? null;
  }

  async function publish(topic, key, payload) {
    published.push({ topic, key, payload });
  }

  async function writeObject(uri, key, value, idempotencyKey) {
    if (typeof uri !== 'string' || typeof key !== 'string') {
      throw new TypeError('writeObject requires uri and key');
    }
    const token = idempotencyKey ? `${uri}#${key}#${idempotencyKey}` : null;
    if (token && idempotencyTokens.has(token)) {
      return;
    }
    ensureBucket(uri).set(key, value);
    if (token) {
      idempotencyTokens.add(token);
    }
  }

  async function readObject(uri, key) {
    const bucket = readBucket(uri);
    if (!bucket) return null;
    return bucket.has(key) ? bucket.get(key) : null;
  }

  async function compareAndSwap(uri, key, expect, update) {
    const bucket = ensureBucket(uri);
    const current = bucket.has(key) ? bucket.get(key) : null;
    if (current !== expect) {
      return false;
    }
    bucket.set(key, update);
    return true;
  }

  async function sign(keyId, data) {
    if (!keyMap.has(keyId)) {
      throw new Error(`Unknown keyId: ${keyId}`);
    }
    const secret = keyMap.get(keyId);
    return createHmac('sha256', secret).update(toBuffer(data)).digest();
  }

  async function verify(keyId, data, sig) {
    if (!keyMap.has(keyId)) {
      return false;
    }
    const expected = await sign(keyId, data);
    const signature = toBuffer(sig);
    if (expected.length !== signature.length) {
      return false;
    }
    return timingSafeEqual(expected, signature);
  }

  async function hash(data) {
    return createHash('sha256').update(toBuffer(data)).digest('hex');
  }

  async function emitMetric(name, value = 1) {
    const numeric = Number.isFinite(value) ? value : 1;
    const current = metrics.get(name) ?? 0;
    metrics.set(name, current + numeric);
  }

  function getPublished() {
    return published.map(clonePublished);
  }

  function getStorageSnapshot() {
    const snapshot = {};
    for (const [uri, bucket] of storage.entries()) {
      snapshot[uri] = Object.fromEntries(bucket.entries());
    }
    return snapshot;
  }

  function getMetricTotals() {
    return Object.fromEntries(metrics.entries());
  }

  function reset() {
    published.length = 0;
    idempotencyTokens.clear();
    storage.clear();
    metrics.clear();
  }

  return {
    publish,
    writeObject,
    readObject,
    compareAndSwap,
    sign,
    verify,
    hash,
    emitMetric,
    getPublished,
    getStorageSnapshot,
    getMetricTotals,
    reset,
  };
}

export default createInmemAdapters;
