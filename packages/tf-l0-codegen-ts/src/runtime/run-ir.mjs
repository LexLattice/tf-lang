const registry = [];
const metaByName = new Map();

function registerMeta(domain, name, primId, effects = []) {
  const entry = {
    domain,
    name,
    prim_id: primId,
    effects: effects.slice(),
    names: []
  };
  const variants = [
    name.toLowerCase(),
    `${domain}/${name}`.toLowerCase(),
    `tf:${domain}/${name}@1`.toLowerCase()
  ];
  entry.names = variants;
  for (const variant of variants) {
    metaByName.set(variant, entry);
  }
  registry.push(entry);
}

registerMeta('resource', 'write-object', 'tf:resource/write-object@1', ['Storage.Write']);
registerMeta('resource', 'read-object', 'tf:resource/read-object@1', ['Storage.Read']);
registerMeta('resource', 'compare-and-swap', 'tf:resource/compare-and-swap@1', ['Storage.Write']);
registerMeta('information', 'hash', 'tf:information/hash@1', ['Pure']);
registerMeta('observability', 'emit-metric', 'tf:observability/emit-metric@1', ['Observability']);
registerMeta('network', 'publish', 'tf:network/publish@1', ['Network.Out']);

function resolveMeta(name) {
  const lower = (name || '').toLowerCase();
  if (metaByName.has(lower)) {
    return metaByName.get(lower);
  }
  const base = lower.split('/').pop()?.split('@')[0] || lower;
  if (metaByName.has(base)) {
    return metaByName.get(base);
  }
  const fallback = registry.find(entry => entry.name === base);
  if (fallback) {
    return fallback;
  }
  return { prim_id: name, effects: [], names: [lower, base].filter(Boolean) };
}

function resolveAdapter(adapters, name) {
  const meta = resolveMeta(name);
  const candidates = Array.from(new Set([...(meta.names || []), (name || '').toLowerCase()]));
  for (const candidate of candidates) {
    const fn = adapters?.[candidate];
    if (typeof fn === 'function') {
      return fn;
    }
  }
  return null;
}

function nowTs() {
  try {
    const clock = globalThis?.__tf_clock;
    if (clock && typeof clock.nowNs === 'function') {
      const raw = clock.nowNs();
      if (typeof raw === 'bigint') {
        return Number(raw / 1_000_000n);
      }
      if (typeof raw === 'number') {
        return Math.floor(raw / 1_000_000);
      }
    }
  } catch {
    // ignore
  }
  return Date.now();
}

async function execNode(node, adapters, ctx) {
  if (!node || typeof node !== 'object') {
    return null;
  }
  if (node.node === 'Prim') {
    const fn = resolveAdapter(adapters, node.prim);
    if (!fn) {
      throw new Error(`No adapter for primitive: ${node.prim}`);
    }
    const meta = resolveMeta(node.prim);
    const ts = nowTs();
    const result = await fn(node.args || {});
    ctx.ops += 1;
    for (const effect of meta.effects || []) {
      ctx.effects.add(effect);
    }
    console.log(JSON.stringify({ prim_id: meta.prim_id || node.prim, args: node.args || {}, ts }));
    return result;
  }
  if (node.node === 'Seq' || node.node === 'Region') {
    let acc = null;
    for (const child of node.children || []) {
      acc = await execNode(child, adapters, ctx);
    }
    return acc;
  }
  if (node.node === 'Par') {
    const results = await Promise.all((node.children || []).map(child => execNode(child, adapters, ctx)));
    return results;
  }
  if (Array.isArray(node.children)) {
    let acc = null;
    for (const child of node.children) {
      acc = await execNode(child, adapters, ctx);
    }
    return acc;
  }
  return null;
}

export async function runIR(ir, adapters) {
  const ctx = { ops: 0, effects: new Set() };
  await execNode(ir, adapters, ctx);
  return { ok: true, ops: ctx.ops, effects: Array.from(ctx.effects) };
}
