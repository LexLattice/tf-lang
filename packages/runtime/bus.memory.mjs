import { randomUUID } from 'node:crypto';
import { deepClone } from '../util/clone.mjs';

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

function makeEntry(topic, message, meta, attempt, retain) {
  return {
    id: meta?.id ?? randomUUID(),
    topic,
    message: deepClone(message),
    meta: {
      ...deepClone(meta ?? {}),
      attempt,
      duplicate: attempt > 1,
      timestamp: Date.now(),
    },
    retain: Boolean(retain),
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
        if (entries.length === 0) {
          queues.delete(topic);
        }
        return deepClone(candidate);
      }
    }
    return null;
  }

  function notify(entry) {
    if (waiters.size === 0) {
      return;
    }
    const resolved = [];
    let delivered = false;
    for (const [id, waiter] of waiters.entries()) {
      if (!matches(waiter.patterns, entry.topic)) {
        continue;
      }
      if (!waiter.filter(entry)) {
        continue;
      }
      resolved.push(id);
      delivered = true;
      waiter.resolve(deepClone(entry));
      break;
    }
    if (delivered && !entry.retain) {
      const queue = queues.get(entry.topic);
      if (queue) {
        const index = queue.findIndex((candidate) => candidate.id === entry.id);
        if (index !== -1) {
          queue.splice(index, 1);
        }
        if (queue.length === 0) {
          queues.delete(entry.topic);
        }
      }
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
    const {
      qos = 'at_least_once',
      duplicates = defaultDuplicates,
      meta = {},
      retain = false,
    } = opts ?? {};
    const totalDuplicates = typeof duplicates === 'number'
      ? Math.max(0, Math.floor(duplicates))
      : duplicates
        ? 1
        : 0;
    const deliveries = [];
    for (let attempt = 1; attempt <= totalDuplicates + 1; attempt += 1) {
      const entry = makeEntry(channel, message, { ...meta, qos }, attempt, retain);
      enqueue(entry);
      notify(entry);
      deliveries.push(deepClone(entry));
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
        state[topic] = entries.map((entry) => deepClone(entry));
      }
      return state;
    }
    const patterns = normalizeChannels(channel);
    const state = {};
    for (const [topic, entries] of queues.entries()) {
      if (!matches(patterns, topic)) {
        continue;
      }
      state[topic] = entries.map((entry) => deepClone(entry));
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
