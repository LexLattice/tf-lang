const PRIM_IDS = {
  'write-object': 'tf:resource/write-object@1',
  'read-object': 'tf:resource/read-object@1',
  'compare-and-swap': 'tf:resource/compare-and-swap@1',
  'hash': 'tf:information/hash@1',
  'emit-metric': 'tf:observability/emit-metric@1',
  'publish': 'tf:network/publish@1',
};

const EFFECTS = {
  'tf:resource/write-object@1': 'Storage.Write',
  'tf:resource/read-object@1': 'Storage.Read',
  'tf:resource/compare-and-swap@1': 'Storage.Write',
  'tf:observability/emit-metric@1': 'Observability',
  'tf:network/publish@1': 'Network.Out',
};

function nowMs() {
  const clock = globalThis.__tf_clock;
  if (clock && typeof clock.nowNs === 'function') {
    try {
      const ns = clock.nowNs();
      if (typeof ns === 'bigint') {
        return Number(ns / 1_000_000n);
      }
      if (typeof ns === 'number') {
        return Math.floor(ns / 1_000_000);
      }
    } catch {
      // fall back to Date.now
    }
  }
  return Date.now();
}

function toPrimId(node) {
  const raw = (node?.prim || '').toLowerCase();
  if (raw.startsWith('tf:')) return raw;
  return PRIM_IDS[raw] || raw;
}

async function executeNode(node, ctx) {
  if (!node || typeof node !== 'object') return null;

  if (node.node === 'Prim') {
    return executePrim(node, ctx);
  }

  if (node.node === 'Seq' || node.node === 'Region') {
    let last = null;
    for (const child of node.children || []) {
      last = await executeNode(child, ctx);
    }
    return last;
  }

  if (node.node === 'Par') {
    const promises = (node.children || []).map((child) => executeNode(child, ctx));
    return Promise.all(promises);
  }

  if (Array.isArray(node.children)) {
    let last = null;
    for (const child of node.children) {
      last = await executeNode(child, ctx);
    }
    return last;
  }

  return null;
}

async function executePrim(node, ctx) {
  const primId = toPrimId(node);
  const adapter = ctx.adapters[primId] || ctx.adapters[node.prim];
  if (typeof adapter !== 'function') {
    throw new Error(`Missing adapter for primitive ${primId || node.prim}`);
  }
  const args = node.args || {};
  const ts = nowMs();
  ctx.ops++;
  const effect = EFFECTS[primId];
  if (effect) ctx.effects.add(effect);
  console.log(JSON.stringify({ prim_id: primId, args, ts }));
  return await adapter(args);
}

export async function runIR(ir, adapters) {
  const ctx = {
    adapters: adapters || {},
    ops: 0,
    effects: new Set(),
  };
  await executeNode(ir, ctx);
  return {
    ok: true,
    ops: ctx.ops,
    effects: Array.from(ctx.effects),
  };
}

export default runIR;
