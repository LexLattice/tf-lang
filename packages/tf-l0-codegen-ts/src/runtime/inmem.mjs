import { createHash } from 'node:crypto';

const storage = new Map();
const metricsLog = [];
const topicQueues = new Map();

function keyFor(uri = '', key = '') {
  return `${uri}#${key}`;
}

function register(target, domain, name, fn) {
  const base = name.toLowerCase();
  const names = [
    base,
    `${domain}/${base}`,
    `tf:${domain}/${base}@1`
  ];
  for (const n of names) {
    target[n] = fn;
  }
}

function ensureTopic(topic) {
  if (!topicQueues.has(topic)) {
    topicQueues.set(topic, []);
  }
  return topicQueues.get(topic);
}

async function writeObject(args = {}) {
  const uri = String(args.uri ?? 'res://unknown');
  const key = String(args.key ?? '');
  const entry = storage.get(keyFor(uri, key));
  const nextEtag = (entry?.etag ?? 0) + 1;
  const value = args.value;
  storage.set(keyFor(uri, key), { value, etag: nextEtag });
  return { ok: true, etag: nextEtag, value };
}

async function readObject(args = {}) {
  const uri = String(args.uri ?? 'res://unknown');
  const key = String(args.key ?? '');
  const entry = storage.get(keyFor(uri, key));
  if (!entry) {
    return { ok: false, value: null, etag: null };
  }
  return { ok: true, value: entry.value, etag: entry.etag };
}

async function compareAndSwap(args = {}) {
  const uri = String(args.uri ?? 'res://unknown');
  const key = String(args.key ?? '');
  const ifMatch = args.ifMatch;
  const current = storage.get(keyFor(uri, key));
  const currentEtag = current?.etag ?? null;
  const matches = ifMatch !== undefined && ifMatch === currentEtag;
  if (!matches) {
    return { ok: false, current: current?.value ?? null, etag: currentEtag };
  }
  const nextEtag = (currentEtag ?? 0) + 1;
  const value = args.value;
  storage.set(keyFor(uri, key), { value, etag: nextEtag });
  return { ok: true, value, etag: nextEtag };
}

async function hashValue(args = {}) {
  const input = 'value' in args ? args.value : args;
  const digest = createHash('sha256')
    .update(JSON.stringify(input))
    .digest('hex');
  return `sha256:${digest}`;
}

async function emitMetric(args = {}) {
  const entry = { ...args, ts: Date.now() };
  metricsLog.push(entry);
  if (process?.env?.DEV_PROOFS) {
    console.log('[metric]', JSON.stringify(entry));
  }
  return { ok: true };
}

async function publish(args = {}) {
  const topic = String(args.topic ?? 'default');
  const queue = ensureTopic(topic);
  queue.push({ key: args.key ?? null, payload: args.payload ?? null, ts: Date.now() });
  return { ok: true };
}

const adapters = {};
register(adapters, 'resource', 'write-object', writeObject);
register(adapters, 'resource', 'read-object', readObject);
register(adapters, 'resource', 'compare-and-swap', compareAndSwap);
register(adapters, 'information', 'hash', hashValue);
register(adapters, 'observability', 'emit-metric', emitMetric);
register(adapters, 'network', 'publish', publish);

export const state = {
  storage,
  metrics: metricsLog,
  topics: topicQueues
};

export default Object.assign({}, adapters, { state });
