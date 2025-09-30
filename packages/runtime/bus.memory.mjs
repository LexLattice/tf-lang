import { randomUUID } from 'node:crypto';

function clone(value) {
  if (value === null || typeof value !== 'object') {
    return value;
  }
  if (Array.isArray(value)) {
    return value.map((item) => clone(item));
  }
  const out = {};
  for (const [key, val] of Object.entries(value)) {
    out[key] = clone(val);
  }
  return out;
}

function escapePattern(pattern) {
  return pattern.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function toRegExp(pattern) {
  if (pattern === '*') {
    return /^.*$/;
  }
  const escaped = escapePattern(pattern).replace(/\\\*/g, '.*');
  return new RegExp(`^${escaped}$`);
}

function normalizeChannels(channel) {
  if (Array.isArray(channel)) {
    return channel.flatMap((item) => normalizeChannels(item));
  }
  const value = channel ?? '*';
  return [
    {
      raw: String(value),
      regex: toRegExp(String(value)),
    },
  ];
}

function buildFilter(filter) {
  if (filter === undefined || filter === null) {
    return () => true;
  }
  if (typeof filter === 'function') {
    return (entry) => {
      try {
        return Boolean(filter(entry.message, entry));
      } catch {
        return false;
      }
    };
  }
  if (typeof filter === 'string' || typeof filter === 'number') {
    const expect = String(filter);
    return (entry) => {
      const msg = entry.message ?? {};
      if (Object.prototype.hasOwnProperty.call(msg, 'corr')) {
        return String(msg.corr) === expect;
      }
      if (msg.payload && Object.prototype.hasOwnProperty.call(msg.payload, 'corr')) {
        return String(msg.payload.corr) === expect;
      }
      return false;
    };
  }
  if (typeof filter === 'object') {
    const checks = Object.entries(filter);
    return (entry) => {
      const msg = entry.message ?? {};
      return checks.every(([key, expect]) => {
        if (Object.prototype.hasOwnProperty.call(msg, key)) {
          return msg[key] === expect;
        }
        if (msg.payload && Object.prototype.hasOwnProperty.call(msg.payload, key)) {
          return msg.payload[key] === expect;
        }
        return false;
      });
    };
  }
  return () => true;
}

function matches(patterns, topic) {
  return patterns.some((pattern) => pattern.regex.test(topic));
}

function makeEntry(topic, message, meta, attempt) {
  return {
    id: meta?.id ?? randomUUID(),
    topic,
    message: clone(message),
    meta: {
      ...clone(meta ?? {}),
      attempt,
      duplicate: attempt > 1,
      timestamp: Date.now(),
    },
  };
}

export function createMemoryBus(options = {}) {
  const {
    defaultDuplicates = 0,
    defaultTimeout = 100,
  } = options;

  const queues = new Map(); // topic -> entries
  const waiters = new Map();
  let waiterSeq = 0;

  function enqueue(entry) {
    if (!queues.has(entry.topic)) {
      queues.set(entry.topic, []);
    }
    queues.get(entry.topic).push(entry);
  }

  function take(patterns, filter) {
    for (const [topic, entries] of queues.entries()) {
      if (!matches(patterns, topic)) {
        continue;
      }
      for (let index = 0; index < entries.length; index += 1) {
        const candidate = entries[index];
        if (!filter(candidate)) {
          continue;
        }
        entries.splice(index, 1);
        return clone(candidate);
      }
    }
    return null;
  }

  function notify(entry) {
    if (waiters.size === 0) {
      return;
    }
    const resolved = [];
    for (const [id, waiter] of waiters.entries()) {
      if (!matches(waiter.patterns, entry.topic)) {
        continue;
      }
      if (!waiter.filter(entry)) {
        continue;
      }
      resolved.push(id);
      waiter.resolve(clone(entry));
    }
    for (const id of resolved) {
      const waiter = waiters.get(id);
      if (waiter?.timer) {
        clearTimeout(waiter.timer);
      }
      waiters.delete(id);
    }
  }

  async function publish(channel, message, opts = {}) {
    if (typeof channel !== 'string' || channel.length === 0) {
      throw new Error('publish requires a non-empty channel string');
    }
    const { qos = 'at_least_once', duplicates = defaultDuplicates, meta = {} } = opts ?? {};
    const totalDuplicates = typeof duplicates === 'number'
      ? Math.max(0, Math.floor(duplicates))
      : duplicates
        ? 1
        : 0;
    const deliveries = [];
    for (let attempt = 1; attempt <= totalDuplicates + 1; attempt += 1) {
      const entry = makeEntry(channel, message, { ...meta, qos }, attempt);
      enqueue(entry);
      notify(entry);
      deliveries.push(clone(entry));
    }
    return deliveries;
  }

  async function receive(channel, opts = {}) {
    const patterns = normalizeChannels(channel ?? '*');
    const filter = buildFilter(opts.filter);
    const timeout = typeof opts.timeout === 'number' && opts.timeout >= 0
      ? opts.timeout
      : defaultTimeout;
    const immediate = take(patterns, filter);
    if (immediate) {
      return immediate;
    }
    return new Promise((resolve, reject) => {
      const id = `waiter:${waiterSeq += 1}`;
      const timer = timeout === 0
        ? null
        : setTimeout(() => {
          waiters.delete(id);
          reject(new Error(`timeout waiting for channel ${patterns.map((p) => p.raw).join(',')}`));
        }, timeout);
      waiters.set(id, { patterns, filter, resolve, reject, timer });
    });
  }

  function snapshot(channel) {
    if (channel === undefined) {
      const state = {};
      for (const [topic, entries] of queues.entries()) {
        state[topic] = entries.map((entry) => clone(entry));
      }
      return state;
    }
    const patterns = normalizeChannels(channel);
    const state = {};
    for (const [topic, entries] of queues.entries()) {
      if (!matches(patterns, topic)) {
        continue;
      }
      state[topic] = entries.map((entry) => clone(entry));
    }
    if (typeof channel === 'string' && !channel.includes('*') && !Array.isArray(channel)) {
      return state[channel] ?? [];
    }
    return state;
  }

  function reset() {
    queues.clear();
    for (const [id, waiter] of waiters.entries()) {
      if (waiter.timer) {
        clearTimeout(waiter.timer);
      }
      waiter.reject(new Error('bus reset'));
      waiters.delete(id);
    }
  }

  return {
    publish,
    receive,
    snapshot,
    reset,
  };
}

export default createMemoryBus;
