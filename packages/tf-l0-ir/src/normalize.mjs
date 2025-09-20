import effects from '../../tf-l0-spec/spec/effects.json' with { type: 'json' };

const DEFAULT_PURE_PRIMS = new Set(
  (effects?.effects || [])
    .filter(entry => Array.isArray(entry.effects) && entry.effects.includes('Pure'))
    .map(entry => shortName(entry.id))
);

export const canon = normalize;

// Minimal normalizer with algebraic rewrites.
export function normalize(ir, lawsSpec = {}) {
  const compiledLaws = compileLaws(lawsSpec);
  return normalizeNode(ir, compiledLaws);
}

function normalizeNode(ir, laws) {
  if (!ir || typeof ir !== 'object') return ir;
  if (ir.node === 'Seq') {
    const flat = [];
    for (const child of ir.children || []) {
      const normalized = normalizeNode(child, laws);
      if (normalized && normalized.node === 'Seq') flat.push(...normalized.children);
      else flat.push(normalized);
    }
    const rewritten = applySeqLaws(flat, laws);
    if (!hasSeqMetadata(ir)) {
      if (rewritten.length === 0) return { node: 'Seq', children: [] };
      if (rewritten.length === 1) return rewritten[0];
    }
    return { ...ir, children: rewritten };
  }
  if (ir.node === 'Par') {
    return { ...ir, children: (ir.children || []).map(child => normalizeNode(child, laws)) };
  }
  if (ir.node === 'Region') {
    return { ...ir, children: (ir.children || []).map(child => normalizeNode(child, laws)) };
  }
  return ir;
}

function applySeqLaws(children, laws) {
  let current = children.slice();
  while (true) {
    const commute = commuteEmitWithPure(current, laws);
    const reduced = reduceIdempotentAndInverse(commute.arr, laws);
    if (!commute.changed && !reduced.changed) return reduced.arr;
    current = reduced.arr;
  }
}

function commuteEmitWithPure(children, laws) {
  const arr = children.slice();
  let changed = false;
  let i = 0;
  while (i < arr.length - 1) {
    if (canCommuteWithPure(arr[i], arr[i + 1], laws)) {
      const tmp = arr[i];
      arr[i] = arr[i + 1];
      arr[i + 1] = tmp;
      changed = true;
      if (i > 0) i--;
      else i++;
    } else {
      i++;
    }
  }
  return { arr, changed };
}

function reduceIdempotentAndInverse(children, laws) {
  const out = [];
  let changed = false;
  for (const child of children) {
    if (!isPrim(child)) {
      out.push(child);
      continue;
    }
    const prev = out[out.length - 1];
    if (isPrim(prev)) {
      if (prev.prim === child.prim && isIdempotentPrim(child.prim, laws)) {
        changed = true;
        continue;
      }
      if (isInversePair(prev.prim, child.prim, laws)) {
        out.pop();
        changed = true;
        continue;
      }
    }
    out.push(child);
  }
  return { arr: out, changed };
}

function canCommuteWithPure(left, right, laws) {
  if (!isPrim(left) || !isPrim(right)) return false;
  return laws.commuteWithPure.has(left.prim) && isPurePrim(right.prim, laws);
}

function isPrim(node) {
  return node && node.node === 'Prim';
}

function hasSeqMetadata(node) {
  if (!node || node.node !== 'Seq') return false;
  for (const key of Object.keys(node)) {
    if (key !== 'node' && key !== 'children') return true;
  }
  return false;
}

function isIdempotentPrim(name, laws) {
  return laws.idempotent.has(name);
}

function isInversePair(a, b, laws) {
  const options = laws.inverses.get(a);
  return options ? options.has(b) : false;
}

function isPurePrim(name, laws) {
  return laws.pure.has(name) || DEFAULT_PURE_PRIMS.has(name);
}

function compileLaws(lawSpec) {
  if (lawSpec && lawSpec.__compiled === true) return lawSpec;
  const idempotent = new Set();
  const inverses = new Map();
  const commuteWithPure = new Set();
  const pure = new Set();

  const addIdempotent = id => {
    const name = shortName(id);
    if (name) idempotent.add(name);
  };

  const addInverse = (first, second) => {
    const a = shortName(first);
    const b = shortName(second);
    if (!a || !b) return;
    if (!inverses.has(a)) inverses.set(a, new Set());
    inverses.get(a).add(b);
  };

  const addCommute = id => {
    const name = shortName(id);
    if (name && name !== 'Pure') commuteWithPure.add(name);
  };

  const addPure = id => {
    const name = shortName(id);
    if (name) pure.add(name);
  };

  if (Array.isArray(lawSpec?.laws)) {
    for (const law of lawSpec.laws) {
      if (!law) continue;
      const applies = Array.isArray(law.applies_to) ? law.applies_to : [];
      switch (law.kind) {
        case 'idempotent':
          applies.forEach(addIdempotent);
          break;
        case 'inverse':
          if (applies.length >= 2) addInverse(applies[0], applies[1]);
          break;
        case 'commuteWithPure':
          applies.forEach(addCommute);
          break;
        case 'pure':
          applies.forEach(addPure);
          break;
        default:
          if (law.kind === 'commutative' && applies.includes('Pure')) {
            applies.forEach(addCommute);
          }
          break;
      }
    }
  }

  if (Array.isArray(lawSpec?.idempotent)) lawSpec.idempotent.forEach(addIdempotent);
  if (Array.isArray(lawSpec?.inverses)) {
    for (const pair of lawSpec.inverses) {
      if (Array.isArray(pair) && pair.length >= 2) addInverse(pair[0], pair[1]);
    }
  }
  if (Array.isArray(lawSpec?.commuteWithPure)) lawSpec.commuteWithPure.forEach(addCommute);
  if (Array.isArray(lawSpec?.pure)) lawSpec.pure.forEach(addPure);

  return { __compiled: true, idempotent, inverses, commuteWithPure, pure };
}

function shortName(id) {
  if (!id || typeof id !== 'string') return id;
  if (id === 'Pure') return 'Pure';
  const slash = id.lastIndexOf('/');
  const at = id.lastIndexOf('@');
  const start = slash >= 0 ? slash + 1 : 0;
  const end = at >= 0 ? at : id.length;
  return id.slice(start, end);
}
