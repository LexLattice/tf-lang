import effectsSpec from '../../tf-l0-spec/spec/effects.json' with { type: 'json' };

const PURE_PRIMS = new Set(
  (effectsSpec?.effects || [])
    .filter(entry => Array.isArray(entry.effects) && entry.effects.includes('Pure'))
    .map(entry => canonicalPrimName(entry.id))
);

export function canon(ir, lawSpec = {}) {
  const config = buildLawConfig(lawSpec);
  return normalizeNode(ir, config);
}

export function normalize(ir, laws = {}) {
  return canon(ir, laws);
}

function normalizeNode(ir, config) {
  if (!ir || typeof ir !== 'object') return ir;
  if (Array.isArray(ir)) return ir.map(node => normalizeNode(node, config));

  if (ir.node === 'Seq') {
    const flattened = [];
    for (const child of ir.children || []) {
      const normalChild = normalizeNode(child, config);
      if (normalChild && normalChild.node === 'Seq') {
        flattened.push(...(normalChild.children || []));
      } else {
        flattened.push(normalChild);
      }
    }
    const rewritten = rewriteSeq(flattened, config);
    if (rewritten.length === 0) return { ...ir, children: rewritten };
    if (rewritten.length === 1) return rewritten[0];
    return { ...ir, children: rewritten };
  }

  if (ir.node === 'Par' || ir.node === 'Region') {
    return {
      ...ir,
      children: (ir.children || []).map(child => normalizeNode(child, config))
    };
  }

  return ir;
}

function rewriteSeq(children, config) {
  let seq = children.slice();
  let changed = true;
  while (changed) {
    changed = false;
    const next = [];
    for (const node of seq) {
      const prev = next[next.length - 1];
      if (prev && prev.node === 'Prim' && node?.node === 'Prim') {
        const prevName = getPrimName(prev);
        const nodeName = getPrimName(node);
        if (prevName && prevName === nodeName && config.idempotent.has(prevName)) {
          changed = true;
          continue;
        }
        if (isInversePair(prevName, nodeName, config)) {
          next.pop();
          changed = true;
          continue;
        }
      }
      next.push(node);
    }
    seq = next;

    for (let i = 0; i < seq.length - 1; i += 1) {
      const a = seq[i];
      const b = seq[i + 1];
      if (a?.node === 'Prim' && b?.node === 'Prim') {
        const aName = getPrimName(a);
        const bName = getPrimName(b);
        if (aName && bName && config.commuteWithPure.has(aName) && isPurePrimName(bName)) {
          const copy = seq.slice();
          copy[i] = b;
          copy[i + 1] = a;
          seq = copy;
          changed = true;
          break;
        }
      }
    }
  }
  return seq;
}

function isInversePair(prevName, nodeName, config) {
  if (!prevName || !nodeName) return false;
  return config.inverses.some(([left, right]) => left === prevName && right === nodeName);
}

function buildLawConfig(raw) {
  const idempotent = new Set();
  const inverses = [];
  const commuteWithPure = new Set();

  const addIdempotent = value => {
    const name = canonicalPrimName(value);
    if (name) idempotent.add(name);
  };

  const addCommute = value => {
    const name = canonicalPrimName(value);
    if (name) commuteWithPure.add(name);
  };

  if (raw && typeof raw === 'object') {
    if (Array.isArray(raw.idempotent)) raw.idempotent.forEach(addIdempotent);
    if (Array.isArray(raw.commuteWithPure)) raw.commuteWithPure.forEach(addCommute);
    if (Array.isArray(raw.inverses)) {
      for (const pair of raw.inverses) {
        if (Array.isArray(pair) && pair.length === 2) {
          const [left, right] = pair.map(canonicalPrimName);
          if (left && right) inverses.push([left, right]);
        }
      }
    }

    if (Array.isArray(raw.laws)) {
      for (const law of raw.laws) {
        if (!law || typeof law !== 'object') continue;
        const kind = law.kind;
        if (kind === 'idempotent') {
          (law.applies_to || []).forEach(addIdempotent);
        } else if (kind === 'inverse' || kind === 'eq') {
          const applies = law.applies_to || [];
          for (const entry of applies) {
            if (Array.isArray(entry) && entry.length === 2) {
              const [left, right] = entry.map(canonicalPrimName);
              if (left && right) inverses.push([left, right]);
            }
          }
          if (applies.length === 2 && typeof applies[0] === 'string' && typeof applies[1] === 'string') {
            const [left, right] = applies.map(canonicalPrimName);
            if (left && right) inverses.push([left, right]);
          }
        } else if (kind === 'commute_with_pure' || kind === 'commute-with-pure' || kind === 'commutative') {
          for (const value of law.applies_to || []) {
            if (typeof value === 'string' && canonicalPrimName(value) !== 'pure') {
              addCommute(value);
            }
          }
        }
      }
    }
  }

  return { idempotent, inverses, commuteWithPure };
}

function getPrimName(node) {
  if (!node || typeof node !== 'object') return '';
  if (typeof node.prim === 'string') return canonicalPrimName(node.prim);
  if (typeof node.id === 'string') return canonicalPrimName(node.id);
  if (typeof node.ref === 'string') return canonicalPrimName(node.ref);
  return '';
}

function canonicalPrimName(value) {
  if (!value || typeof value !== 'string') return '';
  let name = value;
  const slash = name.lastIndexOf('/');
  if (slash >= 0) name = name.slice(slash + 1);
  const at = name.indexOf('@');
  if (at >= 0) name = name.slice(0, at);
  return name.toLowerCase();
}

function isPurePrimName(name) {
  if (!name) return false;
  return PURE_PRIMS.has(name);
}
