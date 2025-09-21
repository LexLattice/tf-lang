import { createWriteStream, mkdirSync } from 'node:fs';
import { dirname } from 'node:path';
import { validateCapabilities } from './capabilities.mjs';

const tracePath = process.env.TF_TRACE_PATH;
let traceOut = null;
if (tracePath) {
  try {
    mkdirSync(dirname(tracePath), { recursive: true });
    traceOut = createWriteStream(tracePath, { flags: 'a' });
  } catch (err) {
    console.warn('tf run-ir: unable to open trace file, falling back to stdout only', err);
    traceOut = null;
  }
}

function emitTrace(rec) {
  const line = JSON.stringify(rec);
  if (traceOut && !traceOut.writableEnded) {
    traceOut.write(line + '\n');
  }
  console.log(line);
}

async function closeTrace() {
  if (!traceOut || traceOut.writableEnded) {
    return;
  }
  const stream = traceOut;
  await new Promise((resolve, reject) => {
    const onError = (err) => {
      stream.off('error', onError);
      reject(err);
    };
    stream.on('error', onError);
    stream.end(() => {
      stream.off('error', onError);
      resolve();
    });
  });
  if (traceOut === stream) {
    traceOut = null;
  }
}

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

function toArray(value) {
  if (!value) return [];
  return Array.isArray(value) ? value : [value];
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
      const effect = effectFor(runtime, node.prim) ?? effectFor(runtime, primId);
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
      emitTrace({ ts, prim_id: primId, args, region, effect: effectTag });
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
  const ctx = { effects: new Set(), ops: 0 };
  try {
    const { value, ok } = await execNode(ir, runtime, ctx, options.input);
    const summary = {
      ok: normalizeOk(ok),
      result: value,
      ops: ctx.ops,
      effects: Array.from(ctx.effects).sort(),
    };
    await closeTrace();
    return summary;
  } catch (err) {
    await closeTrace();
    throw err;
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
