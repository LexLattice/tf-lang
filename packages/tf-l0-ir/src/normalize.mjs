const KNOWN_PURE_PRIMS = new Set(['hash', 'serialize', 'deserialize']);

export function canon(ir, laws = {}) {
  const ctx = buildLawContext(laws);
  return normalizeNode(ir, ctx);
}

// Minimal normalizer: flattens adjacent Seq and applies simple algebraic rewrites.
export function normalize(ir, laws = {}) {
  const ctx = buildLawContext(laws);
  return normalizeNode(ir, ctx);
}

function normalizeNode(ir, ctx) {
  if (!ir || typeof ir !== 'object') return ir;
  if (ir.node === 'Seq') {
    const flattened = [];
    for (const child of ir.children || []) {
      const normalizedChild = normalizeNode(child, ctx);
      if (normalizedChild && normalizedChild.node === 'Seq') {
        flattened.push(...normalizedChild.children);
      } else if (normalizedChild) {
        flattened.push(normalizedChild);
      }
    }
    const simplified = applySeqLaws(flattened, ctx);
    if (simplified.length === 1) return simplified[0];
    return { ...ir, children: simplified };
  }
  if (ir.node === 'Par') {
    return { ...ir, children: (ir.children || []).map((c) => normalizeNode(c, ctx)) };
  }
  if (ir.node === 'Region') {
    return { ...ir, children: (ir.children || []).map((c) => normalizeNode(c, ctx)) };
  }
  return ir;
}

function applySeqLaws(children, ctx) {
  let current = children.slice();
  while (true) {
    const collapsed = collapsePairs(current, ctx);
    const commuted = commuteEmitWithPure(collapsed.nodes, ctx);
    if (!collapsed.changed && !commuted.changed) break;
    current = commuted.nodes;
  }
  return current;
}

function collapsePairs(children, ctx) {
  const out = [];
  let changed = false;
  for (const node of children) {
    const prev = out[out.length - 1];
    if (prev && isPrim(prev) && isPrim(node)) {
      const prevName = primName(prev.prim);
      const nodeName = primName(node.prim);
      if (prevName && nodeName) {
        if (ctx.idempotent.has(prevName) && prevName === nodeName) {
          changed = true;
          continue;
        }
        if (ctx.inverse.get(prevName) === nodeName) {
          out.pop();
          changed = true;
          continue;
        }
      }
    }
    out.push(node);
  }
  return { nodes: out, changed };
}

function commuteEmitWithPure(children, ctx) {
  const nodes = children.slice();
  let changed = false;
  let i = 0;
  while (i < nodes.length - 1) {
    const a = nodes[i];
    const b = nodes[i + 1];
    if (
      isPrim(a) &&
      isPrim(b) &&
      ctx.commuteWithPure.has(primName(a.prim)) &&
      isPurePrim(b, ctx)
    ) {
      nodes[i] = b;
      nodes[i + 1] = a;
      changed = true;
      if (i > 0) {
        i--;
        continue;
      }
    }
    i++;
  }
  return { nodes, changed };
}

function primName(prim) {
  if (typeof prim !== 'string') return undefined;
  const parts = prim.split('/');
  const last = parts[parts.length - 1];
  if (!last) return prim;
  return last.split('@')[0];
}

function isPrim(node) {
  return node && node.node === 'Prim';
}

function buildLawContext(laws) {
  const entries = (laws && laws.laws) || [];
  const idempotent = new Set();
  const inverse = new Map();
  const commuteWithPure = new Set();
  for (const law of entries) {
    const applies = Array.isArray(law?.applies_to) ? law.applies_to : [];
    if (law.kind === 'idempotent') {
      for (const id of applies) {
        const name = primName(id);
        if (name) idempotent.add(name);
      }
    } else if (law.kind === 'inverse' && applies.length >= 2) {
      for (let i = 0; i < applies.length - 1; i++) {
        const left = primName(applies[i]);
        const right = primName(applies[i + 1]);
        if (left && right) {
          inverse.set(left, right);
          inverse.set(right, left);
        }
      }
    } else if (law.kind === 'commute-with-pure') {
      for (const id of applies) {
        if (id === 'Pure') continue;
        const name = primName(id);
        if (name) commuteWithPure.add(name);
      }
    }
  }
  return { idempotent, inverse, commuteWithPure };
}

function isPurePrim(node, ctx) {
  if (!isPrim(node)) return false;
  const name = primName(node.prim);
  if (!name) return false;
  if (Array.isArray(node.meta?.effects) && node.meta.effects.includes('Pure')) return true;
  if (Array.isArray(node.effects) && node.effects.includes('Pure')) return true;
  if (ctx?.pure && ctx.pure.has(name)) return true;
  return KNOWN_PURE_PRIMS.has(name);
}
