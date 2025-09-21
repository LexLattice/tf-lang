import { createWriteStream, mkdirSync } from 'node:fs';
import { dirname } from 'node:path';
import { validateCapabilities } from './capabilities.mjs';
import { createInmemRuntime } from './inmem.mjs';

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
  const activeRuntime = runtime ?? createInmemRuntime();
  if (activeRuntime?.state && typeof activeRuntime.state === 'object') {
    activeRuntime.state.caps = options?.caps ?? null;
  }
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
    const { value, ok } = await execNode(ir, activeRuntime, ctx, options.input);
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
  return runIR(ir, runtime, { caps });
}

export default runIR;
