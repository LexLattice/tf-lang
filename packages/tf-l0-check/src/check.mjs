import { unionEffects } from './lattice.mjs';
import { conflict } from './footprints.mjs';
import {
  effectOf,
  canCommute,
  parSafe,
  primaryFamily
} from './effect-lattice.mjs';

function mergeQos(base = {}, next = {}) {
  const result = { ...base };
  for (const [key, value] of Object.entries(next || {})) {
    if (value === undefined || value === null) {
      continue;
    }
    if (result[key] === undefined) {
      result[key] = value;
    }
  }
  return result;
}

/**
 * Effect/type/footprint checker with conservative fallbacks:
 * - If a primitive has no footprints in catalog, infer minimal reads/writes from args.
 *   This keeps tests green before A2 (footprints) or autofix are applied.
 */
export function checkIR(ir, catalog, options = {}) {
  const ctx = {
    catalog: catalog || { primitives: [] },
    options: options || {},
    envStack: [new Map()]
  };
  return walk(ir, ctx);
}

function walk(node, ctx) {
  if (!node || typeof node !== 'object') {
    return okVerdict();
  }

  if (node.node === 'Let') {
    return handleLet(node, ctx);
  }

  if (node.node === 'Ref') {
    return handleRef(node, ctx);
  }

  if (node.node === 'Prim') {
    return handlePrim(node, ctx);
  }

  if (node.node === 'Seq') {
    return handleSeq(node, ctx);
  }

  if (node.node === 'Par') {
    return handlePar(node, ctx);
  }

  if (node.node === 'Region') {
    pushScope(ctx);
    const verdict = aggregateChildren(node.children || [], ctx);
    popScope(ctx);
    return verdict;
  }

  if (Array.isArray(node.children)) {
    return aggregateChildren(node.children, ctx);
  }

  return okVerdict();
}

function handleLet(node, ctx) {
  const initVerdict = node?.init ? walk(node.init, ctx) : okVerdict();
  const reasons = [...(initVerdict.reasons || [])];

  const topIndex = ctx.envStack.length - 1;
  if (!ctx.envStack[topIndex]) ctx.envStack[topIndex] = new Map();
  const top = ctx.envStack[topIndex];
  const key = normalizeBindingKey(node.name);
  if (key) {
    if (top.has(key)) reasons.push(`LetShadowing: ${node.name}`);
    top.set(key, { loc: node.loc });
  }

  const bodyVerdict = node?.body ? walk(node.body, ctx) : okVerdict();
  let verdict = mergeVerdicts(initVerdict, bodyVerdict);

  if (ctx.options?.flagImpureLet && hasImpureEffects(initVerdict)) {
    reasons.push(`LetImpureInit: ${node.name}`);
  }

  if (reasons.length > 0) {
    verdict.ok = false;
    verdict.reasons = [...verdict.reasons, ...reasons];
  }

  return verdict;
}

function handleRef(node, ctx) {
  if (lookupRef(ctx.envStack, node.name)) {
    return okVerdict();
  }
  return verdictWithReason(`LetUndefined: ${node.name}`);
}

function handlePrim(node, ctx) {
  const name = typeof node.prim === 'string' ? node.prim : '';
  if (!catalogHasPrimitive(name, ctx.catalog)) {
    return verdictWithReason(`UndefinedPrimitive: ${node.raw ?? name}`);
  }

  const prim = lookupWithInference(node, ctx.catalog);
  return {
    ok: true,
    effects: prim.effects || [],
    reads: prim.reads || [],
    writes: prim.writes || [],
    qos: prim.qos || {},
    reasons: []
  };
}

function handleSeq(node, ctx) {
  const isBlock = node.syntax === 'block';
  if (isBlock) pushScope(ctx);

  let acc = okVerdict();
  let prevFamily = null;
  for (const child of node.children || []) {
    const childVerdict = walk(child, ctx);
    acc = mergeVerdicts(acc, childVerdict);

    const currentFamily = nodeFamily(child, childVerdict, ctx.catalog);
    if (typeof child === 'object' && child) {
      child.commutes_with_prev = prevFamily ? canCommute(prevFamily, currentFamily) : false;
    }
    prevFamily = currentFamily || null;
  }

  if (isBlock) popScope(ctx);
  return acc;
}

function handlePar(node, ctx) {
  const children = node.children || [];
  const results = [];
  const families = [];

  for (const child of children) {
    const childCtx = cloneCtx(ctx);
    const verdict = walk(child, childCtx);
    results.push(verdict);
    families.push(nodeFamily(child, verdict, ctx.catalog));
  }

  let acc = okVerdict();
  for (const verdict of results) {
    acc = mergeVerdicts(acc, verdict);
  }

  let ok = results.every((v) => v.ok);
  let conflictDetected = false;

  for (let i = 0; i < results.length; i += 1) {
    for (let j = i + 1; j < results.length; j += 1) {
      if (!parSafe(families[i], families[j], {
        conflict,
        disjoint: ctx.options?.disjoint,
        writesA: results[i].writes,
        writesB: results[j].writes
      })) {
        ok = false;
        conflictDetected = conflictDetected || (families[i] === 'Storage.Write' && families[j] === 'Storage.Write');
      }
    }
  }

  if (!ok) {
    const reason = conflictDetected
      ? 'Par conflict: overlapping writes detected'
      : 'Par effect pair deemed unsafe';
    acc.ok = false;
    acc.reasons = [...acc.reasons, reason];
  }

  return acc;
}

function aggregateChildren(children, ctx) {
  let acc = okVerdict();
  for (const child of children) {
    acc = mergeVerdicts(acc, walk(child, ctx));
  }
  return acc;
}

function cloneVerdict(verdict) {
  return {
    ok: verdict.ok,
    effects: [...(verdict.effects || [])],
    reads: [...(verdict.reads || [])],
    writes: [...(verdict.writes || [])],
    qos: { ...(verdict.qos || {}) },
    reasons: [...(verdict.reasons || [])]
  };
}

function mergeVerdicts(left, right) {
  if (!left) return right || okVerdict();
  if (!right) return left;
  return {
    ok: left.ok && right.ok,
    effects: unionEffects(left.effects || [], right.effects || []),
    reads: [...(left.reads || []), ...(right.reads || [])],
    writes: [...(left.writes || []), ...(right.writes || [])],
    qos: mergeQos(left.qos, right.qos),
    reasons: [...(left.reasons || []), ...(right.reasons || [])]
  };
}

function verdictWithReason(reason) {
  return {
    ok: false,
    effects: [],
    reads: [],
    writes: [],
    qos: {},
    reasons: [reason]
  };
}

function hasImpureEffects(verdict) {
  return (
    (verdict.effects && verdict.effects.length > 0) ||
    (verdict.reads && verdict.reads.length > 0) ||
    (verdict.writes && verdict.writes.length > 0)
  );
}

function pushScope(ctx) {
  ctx.envStack.push(new Map());
}

function popScope(ctx) {
  ctx.envStack.pop();
}

function lookupLet(ctx, name) {
  return lookupRef(ctx.envStack, name);
}

function lookupRef(envStack, name) {
  const key = normalizeBindingKey(name);
  if (!key) return false;
  for (let i = envStack.length - 1; i >= 0; i -= 1) {
    const frame = envStack[i];
    if (frame && frame.has(key)) return true;
  }
  return false;
}

function normalizeBindingKey(name) {
  return typeof name === 'string' ? name.toLowerCase() : '';
}

function catalogHasPrimitive(name, catalog) {
  const target = normalizeBindingKey(name);
  if (!target) return false;
  const list = Array.isArray(catalog?.primitives) ? catalog.primitives : [];
  return list.some((entry) => {
    const entryName = typeof entry?.name === 'string' ? entry.name.toLowerCase() : '';
    if (entryName === target) return true;
    const id = typeof entry?.id === 'string' ? entry.id : '';
    if (!id) return false;
    const parts = id.split('/');
    const last = parts[parts.length - 1] || '';
    const [raw] = last.split('@');
    return typeof raw === 'string' && raw.toLowerCase() === target;
  });
}

function cloneCtx(ctx) {
  return {
    catalog: ctx.catalog,
    options: ctx.options,
    envStack: cloneEnvStack(ctx.envStack)
  };
}

function cloneEnvStack(stack) {
  return stack.map((frame) => new Map(frame));
}

function okVerdict() {
  return { ok: true, effects: [], reads: [], writes: [], qos: {}, reasons: [] };
}

/**
 * Lookup a primitive in the catalog, then (if footprints are absent)
 * infer minimal effects/footprints from the node args.
 */
function lookupWithInference(node, catalog) {
  const primName = (node.prim || '').toLowerCase();
  const hit =
    (catalog.primitives || []).find(
      p => p.name === primName || (p.id || '').endsWith('/' + primName + '@1')
    ) || null;

  let base = hit || {
    id: primName,
    name: primName,
    effects: [],
    reads: [],
    writes: []
  };

  const hasFootprints =
    (base.reads && base.reads.length) || (base.writes && base.writes.length);

  if (!hasFootprints) {
    const inferred = inferFromArgs(primName, node.args || {});
    base = {
      ...base,
      effects: unionEffects(base.effects || [], inferred.effects),
      reads: [...(base.reads || []), ...inferred.reads],
      writes: [...(base.writes || []), ...inferred.writes]
    };
  }

  return base;
}

/**
 * Very small, conservative inference used only when catalog lacks footprints.
 * - read-object/list-objects -> Storage.Read @ uri
 * - write-object/delete-object/compare-and-swap -> Storage.Write @ uri
 * - publish/request/acknowledge -> Network.Out (no footprint needed here)
 * - subscribe -> Network.In
 */
function inferFromArgs(name, args) {
  const uri = args?.uri || args?.resource_uri;
  const hasUri = typeof uri === 'string' && uri.length > 0;
  const mk = mode => ({
    uri: hasUri ? uri : 'res://unknown',
    mode,
    notes: 'inferred'
  });

  const res = { effects: [], reads: [], writes: [] };

  if (/^(read-object|list-objects)$/.test(name)) {
    res.effects.push('Storage.Read');
    res.reads.push(mk('read'));
  }

  if (/^(write-object|delete-object|compare-and-swap)$/.test(name)) {
    res.effects.push('Storage.Write');
    res.writes.push(mk('write'));
  }

  if (/^(publish|request|acknowledge)$/.test(name)) {
    res.effects.push('Network.Out');
  }
  if (/^subscribe$/.test(name)) {
    res.effects.push('Network.In');
  }

  return res;
}

function nodeFamily(node, verdict, catalog) {
  if (!node || typeof node !== 'object') {
    return null;
  }
  if (node.node === 'Prim') {
    const primId = node.id || node.prim;
    return effectOf(primId, catalog);
  }
  return primaryFamily(verdict?.effects || []);
}
