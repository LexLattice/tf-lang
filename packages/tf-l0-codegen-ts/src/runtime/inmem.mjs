import { createHash } from 'node:crypto';

const store = new Map();
let nextEtag = 1;
const metricsLog = [];
const topicQueues = new Map();

function keyFor(uri, key) {
  if (typeof uri !== 'string' || !uri) {
    throw new Error('write-object requires a uri');
  }
  if (typeof key !== 'string' || !key) {
    throw new Error('write-object requires a key');
  }
  return `${uri}#${key}`;
}

function currentTimeMs() {
  const clock = globalThis.__tf_clock;
  if (clock && typeof clock.nowNs === 'function') {
    try {
      const ns = clock.nowNs();
      if (typeof ns === 'bigint') {
        return Number(ns / 1_000_000n);
      }
      if (typeof ns === 'number') {
        return Math.floor(ns / 1_000_000);
      }
    } catch {
      // fall back below
    }
  }
  return Date.now();
}

async function writeObject(args = {}) {
  const { uri, key, value } = args;
  const storageKey = keyFor(uri, key);
  const etag = nextEtag++;
  store.set(storageKey, { value, etag });
  return { ok: true, etag };
}

async function readObject(args = {}) {
  const { uri, key } = args;
  const storageKey = keyFor(uri, key);
  const entry = store.get(storageKey);
  if (!entry) {
    return { ok: false, value: undefined, etag: null };
  }
  return { ok: true, value: entry.value, etag: entry.etag };
}

async function compareAndSwap(args = {}) {
  const { uri, key, value, ifMatch } = args;
  const storageKey = keyFor(uri, key);
  const entry = store.get(storageKey);
  const currentEtag = entry?.etag ?? null;
  if (currentEtag !== ifMatch) {
    return { ok: false, etag: currentEtag, value: entry?.value };
  }
  const etag = nextEtag++;
  store.set(storageKey, { value, etag });
  return { ok: true, etag, value };
}

async function hash(args) {
  const input = args?.value ?? args?.input ?? args;
  const serialized = JSON.stringify(input);
  const digest = createHash('sha256').update(serialized).digest('hex');
  return { ok: true, hash: `sha256:${digest}` };
}

async function emitMetric(args = {}) {
  const payload = { ...args, ts: currentTimeMs() };
  metricsLog.push(payload);
  if (process?.env?.DEV_PROOFS) {
    console.log('[metric]', JSON.stringify(payload));
  }
  return { ok: true };
}

async function publish(args = {}) {
  const { topic, key, payload } = args;
  if (typeof topic !== 'string' || !topic) {
    throw new Error('publish requires topic');
  }
  const queue = topicQueues.get(topic) ?? [];
  queue.push({ key, payload, ts: currentTimeMs() });
  topicQueues.set(topic, queue);
  return { ok: true, size: queue.length };
}

const adapters = {
  'tf:resource/write-object@1': writeObject,
  'tf:resource/read-object@1': readObject,
  'tf:resource/compare-and-swap@1': compareAndSwap,
  'tf:information/hash@1': hash,
  'tf:observability/emit-metric@1': emitMetric,
  'tf:network/publish@1': publish,
};

export const storage = store;
export const metrics = metricsLog;
export const topics = topicQueues;

export default adapters;
