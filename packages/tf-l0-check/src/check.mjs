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
export function checkIR(ir, catalog) {
  return walk(ir, catalog);
}

function walk(node, catalog) {
  if (!node || typeof node !== 'object') {
    return okVerdict();
  }

  if (node.node === 'Prim') {
    const prim = lookupWithInference(node, catalog);
    return {
      ok: true,
      effects: prim.effects || [],
      reads: prim.reads || [],
      writes: prim.writes || [],
      qos: prim.qos || {},
      reasons: []
    };
  }

  if (node.node === 'Seq') {
    let acc = okVerdict();
    let prevFamily = null;
    for (const c of node.children || []) {
      const v = walk(c, catalog);
      acc.ok = acc.ok && v.ok;
      acc.effects = unionEffects(acc.effects, v.effects);
      acc.reads = [...acc.reads, ...(v.reads || [])];
      acc.writes = [...acc.writes, ...(v.writes || [])];
      acc.reasons.push(...(v.reasons || []));
      acc.qos = mergeQos(acc.qos, v.qos);

       const currentFamily = nodeFamily(c, v, catalog);
       if (typeof c === 'object' && c) {
         c.commutes_with_prev = prevFamily ? canCommute(prevFamily, currentFamily) : false;
       }
       prevFamily = currentFamily || null;
    }
    return acc;
  }

  if (node.node === 'Par') {
    const vs = (node.children || []).map(c => walk(c, catalog));
    let ok = vs.every(v => v.ok);
    let qos = {};
    let conflictDetected = false;

    // pairwise conflict check on writes (same resource URI => conflict)
    for (let i = 0; i < vs.length; i++) {
      for (let j = i + 1; j < vs.length; j++) {
        const famA = nodeFamily(node.children?.[i], vs[i], catalog);
        const famB = nodeFamily(node.children?.[j], vs[j], catalog);
        if (!parSafe(famA, famB, {
          conflict,
          writesA: vs[i].writes,
          writesB: vs[j].writes
        })) {
          ok = false;
          conflictDetected = conflictDetected || (famA === 'Storage.Write' && famB === 'Storage.Write');
        }
      }
    }

    for (const v of vs) {
      qos = mergeQos(qos, v.qos);
    }

    return {
      ok,
      effects: vs.reduce((e, v) => unionEffects(e, v.effects), []),
      reads: vs.flatMap(v => v.reads || []),
      writes: vs.flatMap(v => v.writes || []),
      qos,
      reasons: ok
        ? []
        : [conflictDetected ? 'Par conflict: overlapping writes detected' : 'Par effect pair deemed unsafe']
    };
  }

  // Region or unknown nodes just traverse children if present
  if (Array.isArray(node.children)) {
    let acc = okVerdict();
    for (const c of node.children) {
      const v = walk(c, catalog);
      acc.ok = acc.ok && v.ok;
      acc.effects = unionEffects(acc.effects, v.effects);
      acc.reads = [...acc.reads, ...(v.reads || [])];
      acc.writes = [...acc.writes, ...(v.writes || [])];
      acc.reasons.push(...(v.reasons || []));
      acc.qos = mergeQos(acc.qos, v.qos);
    }
    return acc;
  }

  return okVerdict();
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
