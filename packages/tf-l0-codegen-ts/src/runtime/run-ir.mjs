import { createWriteStream, mkdirSync } from 'node:fs';
import { dirname } from 'node:path';
import { createInmemAdapters } from '../adapters/inmem.mjs';
import { validateCapabilities } from './capabilities.mjs';

let clockWarned = false;

function nowTs() {
  const clock = globalThis?.__tf_clock;
  if (clock && typeof clock.nowNs === 'function') {
    try {
      const raw = clock.nowNs();
      if (typeof raw === 'bigint') {
        return Number(raw / 1_000_000n);
      }
      if (typeof raw === 'number') {
        return raw;
      }
    } catch (err) {
      if (!clockWarned) {
        clockWarned = true;
        console.warn('tf run-ir: falling back to Date.now() after clock failure', err);
      }
    }
  }
  return Date.now();
}

function createDeterministicClock() {
  let counter = 0n;
  const base = 1_690_000_000_000_000_000n;
  return {
    nowNs() {
      const value = base + counter * 1_000_000n;
      counter += 1n;
      return value;
    },
  };
}

function toArray(value) {
  if (!value) return [];
  return Array.isArray(value) ? value : [value];
}

const encoder = new TextEncoder();

function isHexString(value) {
  return typeof value === 'string' && value.length % 2 === 0 && /^[0-9a-f]+$/i.test(value);
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }
  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}

function canonicalize(value, seen = new Set()) {
  if (value === null) {
    return null;
  }
  if (value === undefined) {
    return undefined;
  }
  if (typeof value === 'bigint') {
    return value.toString(10);
  }
  if (typeof value !== 'object') {
    return value;
  }
  if (typeof value.toJSON === 'function') {
    return canonicalize(value.toJSON(), seen);
  }
  if (Array.isArray(value)) {
    return value.map((entry) => (entry === undefined ? null : canonicalize(entry, seen)));
  }
  if (!isPlainObject(value)) {
    return value;
  }
  if (seen.has(value)) {
    throw new TypeError('canonicalize: encountered circular reference');
  }
  seen.add(value);
  try {
    const out = {};
    for (const key of Object.keys(value).sort()) {
      const canonical = canonicalize(value[key], seen);
      if (canonical !== undefined) {
        out[key] = canonical;
      }
    }
    return out;
  } finally {
    seen.delete(value);
  }
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

function toNumber(value, fallback = 0) {
  const numeric = Number(value);
  return Number.isFinite(numeric) ? numeric : fallback;
}

const PRIM_SPECS = [
  {
    canonical: 'tf:network/publish@1',
    aliases: ['publish'],
    effect: 'Network.Out',
    method: 'publish',
    optional: false,
    invoke: async (adapters, args = {}) => {
      const topic = normalizeString(args.topic ?? '');
      const key = normalizeString(args.key ?? '');
      const payload = normalizeString(args.payload ?? '');
      await adapters.publish(topic, key, payload);
      return { ok: true };
    },
  },
  {
    canonical: 'tf:observability/emit-metric@1',
    aliases: ['emit-metric'],
    effect: 'Observability.EmitMetric',
    method: 'emitMetric',
    optional: false,
    invoke: async (adapters, args = {}) => {
      const name = normalizeString(args.name ?? args.metric ?? '');
      const value = toNumber(args.value ?? args.amount, 1);
      await adapters.emitMetric(name, value);
      return { ok: true };
    },
  },
  {
    canonical: 'tf:resource/write-object@1',
    aliases: ['write-object'],
    effect: 'Storage.Write',
    method: 'writeObject',
    optional: false,
    invoke: async (adapters, args = {}) => {
      const uri = normalizeString(args.uri ?? '');
      const key = normalizeString(args.key ?? '');
      const value = normalizeString(args.value ?? '');
      const rawIdempotency = args.idempotency_key ?? args.idempotencyKey;
      const idempotencyKey = rawIdempotency === undefined ? undefined : normalizeString(rawIdempotency);
      await adapters.writeObject(uri, key, value, idempotencyKey);
      return { ok: true };
    },
  },
  {
    canonical: 'tf:resource/read-object@1',
    aliases: ['read-object'],
    effect: 'Storage.Read',
    method: 'readObject',
    optional: true,
    invoke: async (adapters, args = {}) => {
      const uri = normalizeString(args.uri ?? '');
      const key = normalizeString(args.key ?? '');
      const value = await adapters.readObject(uri, key);
      if (value === null || value === undefined) {
        return { ok: false, value: null, etag: null };
      }
      return { ok: true, value, etag: null };
    },
  },
  {
    canonical: 'tf:resource/compare-and-swap@1',
    aliases: ['compare-and-swap'],
    effect: 'Storage.Write',
    method: 'compareAndSwap',
    optional: true,
    invoke: async (adapters, args = {}) => {
      const uri = normalizeString(args.uri ?? '');
      const key = normalizeString(args.key ?? '');
      const expectRaw = args.expect ?? args.ifMatch ?? args.match ?? '';
      const updateRaw = args.update ?? args.value ?? '';
      const swapped = await adapters.compareAndSwap(
        uri,
        key,
        normalizeString(expectRaw),
        normalizeString(updateRaw),
      );
      const didSwap = Boolean(swapped);
      return { ok: didSwap, swapped: didSwap };
    },
  },
  {
    canonical: 'tf:information/hash@1',
    aliases: ['hash'],
    effect: 'Pure',
    method: 'hash',
    optional: true,
    invoke: async (adapters, args = {}) => {
      let source;
      if (Object.prototype.hasOwnProperty.call(args, 'data')) {
        source = args.data;
      } else if (Object.prototype.hasOwnProperty.call(args, 'value')) {
        source = args.value;
      } else {
        source = args;
      }
      const digest = await adapters.hash(toUint8Array(source));
      return { ok: true, hash: digest };
    },
  },
  {
    canonical: 'tf:security/sign-data@1',
    aliases: ['sign-data'],
    effect: 'Crypto',
    method: 'sign',
    optional: false,
    invoke: async (adapters, args = {}) => {
      const keyId = normalizeString(args.key_ref ?? args.key ?? args.keyId ?? '');
      let payload;
      if (Object.prototype.hasOwnProperty.call(args, 'data')) {
        payload = args.data;
      } else if (Object.prototype.hasOwnProperty.call(args, 'value')) {
        payload = args.value;
      } else if (Object.prototype.hasOwnProperty.call(args, 'payload')) {
        payload = args.payload;
      } else {
        payload = '';
      }
      const signature = await adapters.sign(keyId, toUint8Array(payload));
      return { ok: true, signature };
    },
  },
  {
    canonical: 'tf:security/verify-signature@1',
    aliases: ['verify-signature'],
    effect: 'Crypto',
    method: 'verify',
    optional: true,
    invoke: async (adapters, args = {}) => {
      const keyId = normalizeString(args.key_ref ?? args.key ?? args.keyId ?? '');
      let payload;
      if (Object.prototype.hasOwnProperty.call(args, 'data')) {
        payload = args.data;
      } else if (Object.prototype.hasOwnProperty.call(args, 'value')) {
        payload = args.value;
      } else if (Object.prototype.hasOwnProperty.call(args, 'payload')) {
        payload = args.payload;
      } else {
        payload = '';
      }
      const signatureRaw = args.signature ?? args.sig ?? args.expected ?? '';
      const ok = await adapters.verify(keyId, toUint8Array(payload), toUint8Array(signatureRaw));
      const verified = Boolean(ok);
      return { ok: verified, verified };
    },
  },
];

const BUILTIN_EFFECTS = new Map();
for (const spec of PRIM_SPECS) {
  BUILTIN_EFFECTS.set(spec.canonical, spec.effect);
  for (const alias of spec.aliases || []) {
    BUILTIN_EFFECTS.set(alias, spec.effect);
  }
}

export function runtimeFromAdapters(adapters) {
  if (!adapters || typeof adapters !== 'object') {
    throw new Error('runtimeFromAdapters: adapters must be an object');
  }
  const adapterMap = Object.create(null);
  const registry = new Map();

  for (const spec of PRIM_SPECS) {
    const impl = adapters[spec.method];
    if (typeof impl !== 'function') {
      if (spec.optional) {
        continue;
      }
      throw new Error(`Missing adapter implementation for ${spec.method}`);
    }
    const handler = async (args = {}, state = {}) => spec.invoke(adapters, args, state);
    const entry = { canonicalId: spec.canonical, effect: spec.effect, impl: handler };
    const names = new Set([spec.canonical, ...(spec.aliases || [])]);
    for (const name of names) {
      registry.set(name, entry);
      adapterMap[name] = handler;
    }
  }

  const runtime = {
    adapters: adapterMap,
    getAdapter(name) {
      return registry.get(name)?.impl ?? null;
    },
    canonicalPrim(name) {
      return registry.get(name)?.canonicalId ?? name;
    },
    effectFor(name) {
      return registry.get(name)?.effect ?? null;
    },
    state: { adapters },
  };

  for (const [name, entry] of registry.entries()) {
    runtime[name] = entry.impl;
  }

  return runtime;
}

function looksLikeAdapterRuntime(value) {
  if (!value || typeof value !== 'object') {
    return false;
  }
  if (typeof value.getAdapter === 'function') {
    return true;
  }
  if (value instanceof Map) {
    return true;
  }
  if (value?.adapters && typeof value.adapters === 'object') {
    return true;
  }
  for (const key of Object.keys(value)) {
    if (typeof value[key] === 'function' && /[:@]/.test(key)) {
      return true;
    }
  }
  return false;
}

function looksLikeTypedAdapters(value) {
  if (!value || typeof value !== 'object') {
    return false;
  }
  const keys = ['publish', 'writeObject', 'readObject', 'compareAndSwap', 'sign', 'verify', 'hash', 'emitMetric'];
  return keys.some((key) => typeof value[key] === 'function');
}

function prepareRuntime(runtime) {
  if (looksLikeAdapterRuntime(runtime)) {
    return runtime;
  }
  if (looksLikeTypedAdapters(runtime)) {
    return runtimeFromAdapters(runtime);
  }
  if (runtime && typeof runtime === 'object') {
    for (const key of Object.keys(runtime)) {
      if (typeof runtime[key] === 'function') {
        return runtime;
      }
    }
  }
  const instance = createInmemAdapters();
  const wrapped = runtimeFromAdapters(instance.adapters);
  wrapped.state = {
    adapters: instance.adapters,
    getPublished: instance.getPublished,
    getMetrics: instance.getMetrics,
    getStorageSnapshot: instance.getStorageSnapshot,
    reset: instance.reset,
  };
  wrapped.reset = instance.reset;
  wrapped.getPublished = instance.getPublished;
  wrapped.getMetrics = instance.getMetrics;
  wrapped.getStorageSnapshot = instance.getStorageSnapshot;
  return wrapped;
}

function resolveAdapter(runtime, prim) {
  if (!runtime) return null;
  if (typeof runtime.getAdapter === 'function') {
    const adapter = runtime.getAdapter(prim);
    if (adapter) return adapter;
  }
  if (runtime instanceof Map && runtime.has(prim)) {
    return runtime.get(prim);
  }
  if (runtime?.adapters && typeof runtime.adapters[prim] === 'function') {
    return runtime.adapters[prim];
  }
  if (typeof runtime[prim] === 'function') {
    return runtime[prim];
  }
  return null;
}

function canonicalPrim(runtime, prim) {
  if (runtime && typeof runtime.canonicalPrim === 'function') {
    return runtime.canonicalPrim(prim);
  }
  return prim;
}

function effectFor(runtime, prim) {
  if (!runtime) return null;
  if (typeof runtime.effectFor === 'function') {
    return runtime.effectFor(prim);
  }
  if (runtime?.effects && prim in runtime.effects) {
    return runtime.effects[prim];
  }
  return null;
}

function recordEffects(target, value) {
  for (const entry of toArray(value)) {
    if (entry) {
      target.add(entry);
    }
  }
}

function normalizeOk(value) {
  return typeof value === 'boolean' ? value : true;
}

async function execNode(node, runtime, ctx, input) {
  if (!node || typeof node !== 'object') {
    return { value: input, ok: true };
  }
  switch (node.node) {
    case 'Prim': {
      const adapter = resolveAdapter(runtime, node.prim);
      if (typeof adapter !== 'function') {
        throw new Error(`No adapter for primitive "${node.prim}"`);
      }
      const args = node.args ?? {};
      const primId = canonicalPrim(runtime, node.prim);
      const ts = nowTs();
      ctx.ops += 1;
      const result = await adapter(args, runtime?.state ?? {});
      const effect =
        effectFor(runtime, node.prim) ??
        effectFor(runtime, primId) ??
        BUILTIN_EFFECTS.get(node.prim) ??
        BUILTIN_EFFECTS.get(primId);
      const region = typeof node.meta?.region === 'string' ? node.meta.region : '';
      let effectTag = '';
      if (typeof effect === 'string') {
        effectTag = effect;
      } else if (typeof node.meta?.effect === 'string') {
        effectTag = node.meta.effect;
      } else if (Array.isArray(node.meta?.effects)) {
        const first = node.meta.effects.find((entry) => typeof entry === 'string');
        if (first) effectTag = first;
      }
      if (effect) recordEffects(ctx.effects, effect);
      if (node.meta?.effect) recordEffects(ctx.effects, node.meta.effect);
      if (node.meta?.effects) recordEffects(ctx.effects, node.meta.effects);
      const emit = ctx.emit;
      if (typeof emit === 'function') {
        emit({ ts, prim_id: primId, args, region, effect: effectTag });
      }
      const ok = normalizeOk(result?.ok);
      return { value: result, ok };
    }
    case 'Region': // fallthrough
    case 'Seq': {
      let acc = input;
      let ok = true;
      const children = node.children ?? [];
      if (children.length === 0) {
        return { value: acc, ok };
      }
      for (const child of children) {
        const result = await execNode(child, runtime, ctx, acc);
        acc = result.value;
        ok = normalizeOk(result.ok);
      }
      return { value: acc, ok };
    }
    case 'Par': {
      const children = node.children ?? [];
      const results = await Promise.all(children.map((child) => execNode(child, runtime, ctx, input)));
      const ok = results.every((entry) => normalizeOk(entry.ok));
      return { value: results.map((entry) => entry.value), ok };
    }
    default: {
      if (Array.isArray(node.children)) {
        let acc = input;
        let ok = true;
        for (const child of node.children) {
          const result = await execNode(child, runtime, ctx, acc);
          acc = result.value;
          ok = normalizeOk(result.ok);
        }
        return { value: acc, ok };
      }
      return { value: input, ok: true };
    }
  }
}

export async function runIR(ir, runtime, options = {}) {
  const effectiveRuntime = prepareRuntime(runtime);
  const tracePath = process.env.TF_TRACE_PATH;
  let traceStream = null;
  let traceWritable = false;
  let traceWarned = false;
  const globalRef = typeof globalThis === 'object' ? globalThis : undefined;
  const hadClock = Boolean(globalRef && Object.prototype.hasOwnProperty.call(globalRef, '__tf_clock'));
  const previousClock = hadClock ? globalRef.__tf_clock : undefined;
  let assignedClock = false;

  if (globalRef && (!previousClock || typeof previousClock?.nowNs !== 'function')) {
    globalRef.__tf_clock = createDeterministicClock();
    assignedClock = true;
  }

  if (tracePath) {
    try {
      mkdirSync(dirname(tracePath), { recursive: true });
    } catch (err) {
      console.warn('tf run-ir: unable to prepare trace directory', err);
    }
    try {
      traceStream = createWriteStream(tracePath, { flags: 'a' });
      traceWritable = true;
      traceStream.once('error', (err) => {
        if (!traceWarned) {
          traceWarned = true;
          console.warn('tf run-ir: trace writer disabled after error', err);
        }
        traceWritable = false;
      });
    } catch (err) {
      traceStream = null;
      console.warn('tf run-ir: unable to open trace file, falling back to stdout only', err);
    }
  }

  const includeMeta = process.env.TF_PROVENANCE === '1' && options?.traceMeta;
  const metaPayload = includeMeta ? { ...options.traceMeta } : null;
  const emit = (rec) => {
    const entry = {
      ts: rec.ts,
      prim_id: rec.prim_id,
      args: rec.args,
      region: rec.region,
      effect: rec.effect,
    };
    if (metaPayload) {
      entry.meta = metaPayload;
    }
    const line = JSON.stringify(entry);
    console.log(line);
    if (traceWritable && traceStream && !traceStream.destroyed && !traceStream.writableEnded) {
      try {
        traceStream.write(`${line}\n`);
      } catch (err) {
        if (!traceWarned) {
          traceWarned = true;
          console.warn('tf run-ir: trace writer disabled after error', err);
        }
        traceWritable = false;
      }
    }
  };

  const ctx = { effects: new Set(), ops: 0, emit };
  try {
    const { value, ok } = await execNode(ir, effectiveRuntime, ctx, options.input);
    return {
      ok: normalizeOk(ok),
      result: value,
      ops: ctx.ops,
      effects: Array.from(ctx.effects).sort(),
      provenance: options?.provenance ? { ...options.provenance } : null,
    };
  } finally {
    if (traceStream && !traceStream.destroyed && !traceStream.writableEnded) {
      await new Promise((resolve) => {
        traceStream.end(() => resolve());
      });
    }
    if (assignedClock && globalRef) {
      if (hadClock) {
        globalRef.__tf_clock = previousClock;
      } else {
        delete globalRef.__tf_clock;
      }
    }
  }
}

export async function runWithCaps(ir, runtime, caps, manifest) {
  const verdict = validateCapabilities(manifest, caps);
  if (!verdict.ok) {
    console.error('tf run-ir: capability validation failed', JSON.stringify(verdict));
    return { ok: false, ops: 0, effects: [], result: undefined };
  }
  return runIR(ir, runtime);
}

export default runIR;
