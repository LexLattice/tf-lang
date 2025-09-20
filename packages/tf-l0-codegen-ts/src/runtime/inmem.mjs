import { createHash } from 'node:crypto';

const storage = new Map();
const metricsLog = [];
const topicQueues = new Map();
const registry = new Map();
const handlers = Object.create(null);

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

function keyFor(uri, key) {
  return `${uri}#${key}`;
}

function nextEtag(current) {
  return (Number.isFinite(current) ? Number(current) : 0) + 1;
}

function register(canonicalId, aliases, effect, impl) {
  const entry = { canonicalId, effect, impl };
  const names = new Set([canonicalId, ...(aliases || [])]);
  for (const name of names) {
    registry.set(name, entry);
    handlers[name] = impl;
  }
}

register('tf:resource/write-object@1', ['write-object'], 'Storage.Write', async ({ uri, key, value }) => {
  const storageKey = keyFor(uri, key);
  const current = storage.get(storageKey);
  const etag = nextEtag(current?.etag);
  storage.set(storageKey, { value, etag });
  return { ok: true, etag };
});

register('tf:resource/read-object@1', ['read-object'], 'Storage.Read', async ({ uri, key }) => {
  const storageKey = keyFor(uri, key);
  const current = storage.get(storageKey);
  if (!current) {
    return { ok: false, value: null, etag: null };
  }
  return { ok: true, value: current.value, etag: current.etag };
});

register('tf:resource/compare-and-swap@1', ['compare-and-swap'], 'Storage.Write', async ({ uri, key, value, ifMatch }) => {
  const storageKey = keyFor(uri, key);
  const current = storage.get(storageKey);
  if (!current) {
    return { ok: false, etag: null };
  }
  const matches = String(current.etag) === String(ifMatch);
  if (!matches) {
    return { ok: false, etag: current.etag };
  }
  const etag = nextEtag(current.etag);
  storage.set(storageKey, { value, etag });
  return { ok: true, etag };
});

register('tf:information/hash@1', ['hash'], 'Information.Hash', async (args = {}) => {
  const target = Object.prototype.hasOwnProperty.call(args, 'value') ? args.value : args;
  const s = stableStringify(target);
  const digest = createHash('sha256').update(s).digest('hex');
  return { ok: true, hash: `sha256:${digest}` };
});

register('tf:observability/emit-metric@1', ['emit-metric'], 'Observability.EmitMetric', async (args = {}) => {
  metricsLog.push(args);
  if (process.env.DEV_PROOFS) {
    console.log('[metric]', JSON.stringify(args));
  }
  return { ok: true };
});

register('tf:network/publish@1', ['publish'], 'Network.Publish', async (args = {}) => {
  const topic = args.topic ?? 'default';
  if (!topicQueues.has(topic)) {
    topicQueues.set(topic, []);
  }
  topicQueues.get(topic).push(args);
  return { ok: true };
});

function effectFor(name) {
  const entry = registry.get(name);
  return entry?.effect ?? null;
}

const inmem = handlers;

inmem.getAdapter = function getAdapter(name) {
  return registry.get(name)?.impl ?? null;
};

inmem.canonicalPrim = function canonicalPrim(name) {
  return registry.get(name)?.canonicalId ?? name;
};

inmem.effectFor = effectFor;

inmem.state = {
  storage,
  metrics: metricsLog,
  topics: topicQueues,
};

inmem.reset = function reset() {
  storage.clear();
  metricsLog.length = 0;
  topicQueues.clear();
};

export default inmem;
