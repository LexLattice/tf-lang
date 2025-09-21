import { createWriteStream, mkdirSync } from 'node:fs';
import { dirname } from 'node:path';
import { validateCapabilities } from './capabilities.mjs';

function createTraceWriter(tracePath) {
  if (!tracePath) {
    return null;
  }

  try {
    mkdirSync(dirname(tracePath), { recursive: true });
  } catch (err) {
    console.warn('tf run-ir: unable to prepare trace directory', err);
  }

  let stream;
  try {
    stream = createWriteStream(tracePath, { flags: 'a' });
  } catch (err) {
    console.warn('tf run-ir: unable to open trace file, falling back to stdout only', err);
    return null;
  }

  let warned = false;
  let writable = true;

  const handleError = (err) => {
    if (!warned) {
      warned = true;
      console.warn('tf run-ir: trace writer disabled after error', err);
    }
    writable = false;
  };

  stream.once('error', handleError);

  return {
    write(line) {
      if (!writable || !stream || stream.destroyed || stream.writableEnded) {
        return;
      }
      try {
        stream.write(line);
      } catch (err) {
        handleError(err);
      }
    },
    async close() {
      if (!stream || stream.destroyed || stream.writableEnded) {
        return;
      }
      await new Promise((resolve) => {
        const done = () => resolve();
        stream.once('error', done);
        stream.end(() => resolve());
      });
    },
  };
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
  const writer = createTraceWriter(process.env.TF_TRACE_PATH);
  const provenance = sanitizeProvenance(options?.provenance);
  const traceMeta =
    process.env.TF_PROVENANCE === '1' && provenance
      ? buildTraceMeta(provenance)
      : null;
  const emit = (rec) => {
    const entry = {
      ts: rec.ts,
      prim_id: rec.prim_id,
      args: rec.args,
      region: rec.region,
      effect: rec.effect,
    };
    if (traceMeta) {
      entry.meta = traceMeta;
    }
    const line = JSON.stringify(entry);
    console.log(line);
    if (writer) {
      writer.write(`${line}\n`);
    }
  };

  const ctx = { effects: new Set(), ops: 0, emit };
  try {
    const { value, ok } = await execNode(ir, runtime, ctx, options.input);
    return {
      ok: normalizeOk(ok),
      result: value,
      ops: ctx.ops,
      effects: Array.from(ctx.effects).sort(),
      provenance: provenance ?? null,
    };
  } finally {
    if (writer) {
      await writer.close();
    }
  }
}

function sanitizeProvenance(raw) {
  if (!raw || typeof raw !== 'object') return null;
  const out = {};
  if (typeof raw.ir_hash === 'string' && raw.ir_hash) {
    out.ir_hash = raw.ir_hash;
  }
  if (typeof raw.manifest_hash === 'string' && raw.manifest_hash) {
    out.manifest_hash = raw.manifest_hash;
  }
  if (typeof raw.catalog_hash === 'string' && raw.catalog_hash) {
    out.catalog_hash = raw.catalog_hash;
  }
  if (typeof raw.caps_source === 'string' && raw.caps_source) {
    out.caps_source = raw.caps_source;
  }
  if (Array.isArray(raw.caps_effects)) {
    out.caps_effects = raw.caps_effects.filter((entry) => typeof entry === 'string');
  }
  return Object.keys(out).length > 0 ? out : null;
}

function buildTraceMeta(provenance) {
  const meta = {};
  if (typeof provenance.ir_hash === 'string') {
    meta.ir_hash = provenance.ir_hash;
  }
  if (typeof provenance.manifest_hash === 'string') {
    meta.manifest_hash = provenance.manifest_hash;
  }
  if (typeof provenance.catalog_hash === 'string') {
    meta.catalog_hash = provenance.catalog_hash;
  }
  return Object.keys(meta).length > 0 ? meta : null;
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
