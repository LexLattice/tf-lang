import { createHash } from 'node:crypto';

const storage = new Map();
const metrics = [];
const topics = new Map();

function keyFor(uri = '', key = '') {
  return `${uri}#${key}`;
}

function ensureRecord(uri, key) {
  const k = keyFor(uri, key);
  if (!storage.has(k)) {
    storage.set(k, { value: undefined, etag: 0 });
  }
  return storage.get(k);
}

function nextEtag(record) {
  const current = typeof record?.etag === 'number' ? record.etag : 0;
  return current + 1;
}

function toCanonicalTopic(args = {}) {
  return args.topic || args.uri || 'default';
}

const adapters = {
  'tf:resource/write-object@1': async (args = {}) => {
    const { uri = '', key = '', value } = args;
    const record = ensureRecord(uri, key);
    const etag = nextEtag(record);
    storage.set(keyFor(uri, key), { value, etag });
    return { ok: true, etag };
  },
  'tf:resource/read-object@1': async (args = {}) => {
    const { uri = '', key = '' } = args;
    const record = storage.get(keyFor(uri, key));
    if (!record) {
      return { found: false, value: undefined, etag: 0 };
    }
    return { found: true, value: record.value, etag: record.etag };
  },
  'tf:resource/compare-and-swap@1': async (args = {}) => {
    const { uri = '', key = '', value, new_value, newValue, ifMatch } = args;
    const record = storage.get(keyFor(uri, key));
    const currentEtag = record?.etag ?? 0;
    if (ifMatch !== currentEtag) {
      return { ok: false, etag: currentEtag, conflict: true };
    }
    const nextValue = new_value ?? newValue ?? value;
    const etag = currentEtag + 1;
    storage.set(keyFor(uri, key), { value: nextValue, etag });
    return { ok: true, etag, value: nextValue };
  },
  'tf:information/hash@1': async (args = {}) => {
    const input = Object.prototype.hasOwnProperty.call(args, 'value') ? args.value : args.input ?? args.data ?? null;
    const payload = JSON.stringify(input);
    const digest = createHash('sha256').update(payload).digest('hex');
    return { hash: `sha256:${digest}` };
  },
  'tf:observability/emit-metric@1': async (args = {}) => {
    metrics.push({ ts: Date.now(), args });
    if (process.env.DEV_PROOFS) {
      console.log('[metric]', JSON.stringify(args));
    }
    return { ok: true };
  },
  'tf:network/publish@1': async (args = {}) => {
    const topic = toCanonicalTopic(args);
    const queue = topics.get(topic) || [];
    queue.push({ ts: Date.now(), args });
    topics.set(topic, queue);
    return { ok: true };
  }
};

export default adapters;
export { storage, metrics, topics };

