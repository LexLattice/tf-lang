import effects from '../../tf-l0-spec/spec/effects.json' with { type: 'json' };

const PURE_PRIMS = new Set((effects.effects || [])
  .filter(entry => Array.isArray(entry.effects) && entry.effects.includes('Pure'))
  .map(entry => extractPrimName(entry.id))
  .filter(Boolean));

export function canon(ir, lawsSpec = {}) {
  const config = prepareLawConfig(lawsSpec);
  return normalizeNode(ir, config);
}

export function normalize(ir, lawsSpec = {}) {
  return canon(ir, lawsSpec);
}

function normalizeNode(ir, laws) {
  if (!ir || typeof ir !== 'object') return ir;
  if (ir.node === 'Seq') {
    const flat = [];
    for (const child of ir.children || []) {
      const normalized = normalizeNode(child, laws);
      if (normalized && normalized.node === 'Seq') {
        flat.push(...(normalized.children || []));
      } else if (normalized !== undefined) {
        flat.push(normalized);
      }
    }
    const rewritten = rewriteSeq(flat, laws);
    if (rewritten.length === 1) {
      return rewritten[0];
    }
    return { ...ir, children: rewritten };
  }
  if (ir.node === 'Par') {
    return { ...ir, children: (ir.children || []).map(child => normalizeNode(child, laws)) };
  }
  if (ir.node === 'Region') {
    return {
      ...ir,
      children: (ir.children || []).map(child => normalizeNode(child, laws))
    };
  }
  return ir;
}

function rewriteSeq(children, laws) {
  const out = [...children];
  let changed = true;
  while (changed) {
    changed = false;
    for (let i = 0; i < out.length; i++) {
      const current = out[i];
      if (!isPrim(current)) continue;
      const currentName = extractPrimName(current.prim);
      const next = out[i + 1];

      if (next && isPrim(next)) {
        const nextName = extractPrimName(next.prim);

        if (currentName && nextName && currentName === nextName && laws.idempotent.has(currentName)) {
          out.splice(i + 1, 1);
          changed = true;
          i = Math.max(i - 1, -1);
          continue;
        }

        if (currentName && nextName && laws.inverse.has(pairKey(currentName, nextName))) {
          out.splice(i, 2);
          changed = true;
          i = Math.max(i - 1, -1);
          continue;
        }

        if (currentName && laws.commuteWithPure.has(currentName) && nextName && isPurePrim(nextName, laws)) {
          [out[i], out[i + 1]] = [out[i + 1], out[i]];
          changed = true;
          i = Math.max(i - 1, -1);
          continue;
        }
      }
    }
  }
  return out;
}

function isPrim(node) {
  return Boolean(node && typeof node === 'object' && node.node === 'Prim');
}

function extractPrimName(id) {
  if (typeof id !== 'string' || id.length === 0) return null;
  if (id.includes('/')) {
    const segment = id.split('/').pop() || '';
    return segment.split('@')[0].toLowerCase();
  }
  return id.toLowerCase();
}

function prepareLawConfig(lawSpec) {
  const config = {
    idempotent: new Set(),
    inverse: new Set(),
    commuteWithPure: new Set(),
    pure: new Set(PURE_PRIMS)
  };

  if (!lawSpec || typeof lawSpec !== 'object') {
    return config;
  }

  const lawList = Array.isArray(lawSpec.laws) ? lawSpec.laws : [];
  for (const law of lawList) {
    if (!law || typeof law !== 'object') continue;
    const applies = Array.isArray(law.applies_to) ? law.applies_to : [];
    switch (law.kind) {
      case 'idempotent':
        for (const id of applies) {
          const name = extractPrimName(id);
          if (name) config.idempotent.add(name);
        }
        break;
      case 'inverse':
        if (applies.length >= 2) {
          const a = extractPrimName(applies[0]);
          const b = extractPrimName(applies[1]);
          if (a && b) config.inverse.add(pairKey(a, b));
        }
        break;
      case 'commute_with_pure':
      case 'commuteWithPure':
      case 'commutative':
        for (const id of applies) {
          const name = extractPrimName(id);
          if (name && name !== 'pure') config.commuteWithPure.add(name);
        }
        break;
      default:
        break;
    }
  }

  const idempotentList = Array.isArray(lawSpec.idempotent) ? lawSpec.idempotent : [];
  for (const id of idempotentList) {
    const name = extractPrimName(id);
    if (name) config.idempotent.add(name);
  }

  const inverseList = Array.isArray(lawSpec.inverses) ? lawSpec.inverses : [];
  for (const pair of inverseList) {
    if (!Array.isArray(pair) || pair.length < 2) continue;
    const a = extractPrimName(pair[0]);
    const b = extractPrimName(pair[1]);
    if (a && b) config.inverse.add(pairKey(a, b));
  }

  const commuteList = Array.isArray(lawSpec.commuteWithPure) ? lawSpec.commuteWithPure : [];
  for (const id of commuteList) {
    const name = extractPrimName(id);
    if (name) config.commuteWithPure.add(name);
  }

  const pureList = Array.isArray(lawSpec.pure) ? lawSpec.pure : [];
  for (const id of pureList) {
    const name = extractPrimName(id);
    if (name) config.pure.add(name);
  }

  return config;
}

function isPurePrim(name, laws) {
  if (!name) return false;
  return laws.pure.has(name);
}

function pairKey(a, b) {
  return `${a}|${b}`;
}
