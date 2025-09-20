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
    } catch {
      // fall through to Date.now()
    }
  }
  return Date.now();
}

function toArray(value) {
  if (!value) return [];
  return Array.isArray(value) ? value : [value];
}

function recordEffect(target, value) {
  for (const entry of toArray(value)) {
    if (entry && !target.includes(entry)) {
      target.push(entry);
    }
  }
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

async function execNode(node, runtime, ctx, input) {
  if (!node || typeof node !== 'object') return input;
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
      if (effect) recordEffect(ctx.effects, effect);
      if (node.meta?.effect) recordEffect(ctx.effects, node.meta.effect);
      if (node.meta?.effects) recordEffect(ctx.effects, node.meta.effects);
      console.log(JSON.stringify({ prim_id: primId, args, ts }));
      return result;
    }
    case 'Seq': {
      let acc = input;
      for (const child of node.children ?? []) {
        acc = await execNode(child, runtime, ctx, acc);
      }
      return acc;
    }
    case 'Par': {
      const children = node.children ?? [];
      return await Promise.all(children.map((child) => execNode(child, runtime, ctx, input)));
    }
    case 'Region': {
      let acc = input;
      for (const child of node.children ?? []) {
        acc = await execNode(child, runtime, ctx, acc);
      }
      return acc;
    }
    default: {
      if (Array.isArray(node.children)) {
        let acc = input;
        for (const child of node.children) {
          acc = await execNode(child, runtime, ctx, acc);
        }
        return acc;
      }
      return input;
    }
  }
}

export async function runIR(ir, runtime, options = {}) {
  const ctx = { effects: [], ops: 0 };
  const result = await execNode(ir, runtime, ctx, options.input);
  return { ok: true, result, ops: ctx.ops, effects: ctx.effects };
}

export default runIR;
