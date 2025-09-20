const PRIM_ALIASES = {
  'write-object': 'tf:resource/write-object@1',
  'tf:resource/write-object@1': 'tf:resource/write-object@1',
  'read-object': 'tf:resource/read-object@1',
  'tf:resource/read-object@1': 'tf:resource/read-object@1',
  'compare-and-swap': 'tf:resource/compare-and-swap@1',
  'tf:resource/compare-and-swap@1': 'tf:resource/compare-and-swap@1',
  'hash': 'tf:information/hash@1',
  'tf:information/hash@1': 'tf:information/hash@1',
  'emit-metric': 'tf:observability/emit-metric@1',
  'tf:observability/emit-metric@1': 'tf:observability/emit-metric@1',
  'publish': 'tf:network/publish@1',
  'tf:network/publish@1': 'tf:network/publish@1'
};

const PRIM_EFFECTS = {
  'tf:resource/write-object@1': ['Storage.Write'],
  'tf:resource/read-object@1': ['Storage.Read'],
  'tf:resource/compare-and-swap@1': ['Storage.Write'],
  'tf:information/hash@1': ['Pure'],
  'tf:observability/emit-metric@1': ['Observability'],
  'tf:network/publish@1': ['Network.Out']
};

function canonicalPrim(prim) {
  if (!prim) return prim;
  const lowered = typeof prim === 'string' ? prim.toLowerCase() : prim;
  return PRIM_ALIASES[lowered] || prim;
}

function nowTimestamp() {
  const clock = globalThis.__tf_clock;
  try {
    if (clock && typeof clock.nowMs === 'function') {
      return Number(clock.nowMs());
    }
    if (clock && typeof clock.nowNs === 'function') {
      const ns = clock.nowNs();
      if (typeof ns === 'bigint') {
        return Number(ns / 1_000_000n);
      }
      return Number(ns) / 1_000_000;
    }
  } catch {
    // fall back to Date.now
  }
  return Date.now();
}

async function evalNode(node, ctx) {
  if (!node || typeof node !== 'object') {
    return null;
  }

  if (node.node === 'Prim') {
    return await execPrim(node, ctx);
  }

  if (node.node === 'Seq') {
    let last = null;
    for (const child of node.children || []) {
      last = await evalNode(child, ctx);
    }
    return last;
  }

  if (node.node === 'Par') {
    const promises = (node.children || []).map(child => evalNode(child, ctx));
    return await Promise.all(promises);
  }

  if (node.node === 'Region' || Array.isArray(node.children)) {
    let last = null;
    for (const child of node.children || []) {
      last = await evalNode(child, ctx);
    }
    return last;
  }

  return null;
}

async function execPrim(node, ctx) {
  const primId = canonicalPrim(node.prim);
  const handler = ctx.adapters[primId] || ctx.adapters[node.prim];
  if (typeof handler !== 'function') {
    throw new Error(`No adapter for primitive: ${node.prim}`);
  }
  const args = node.args || {};
  const ts = nowTimestamp();
  const result = await handler(args, ctx);
  ctx.ops++;
  const effects = PRIM_EFFECTS[primId] || [];
  for (const eff of effects) ctx.effects.add(eff);
  const line = { prim_id: primId, args, ts };
  console.log(JSON.stringify(line));
  return result;
}

export async function runIR(ir, adapters) {
  const ctx = {
    adapters: adapters || {},
    ops: 0,
    effects: new Set()
  };
  await evalNode(ir, ctx);
  return {
    ok: true,
    ops: ctx.ops,
    effects: Array.from(ctx.effects)
  };
}

