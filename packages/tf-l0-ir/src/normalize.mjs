import { normalizeByCommutation } from './normalize-commute.mjs';

const KNOWN_PURE_PRIMS = new Set(['hash', 'serialize', 'deserialize']);

export function canon(ir, laws = {}, options = {}) {
  const ctx = buildLawContext(laws);
  const normalized = normalizeNode(ir, ctx);
  const catalog = options?.catalog ?? laws?.catalog;
  return normalizeByCommutation(normalized, catalog);
}

export function normalize(ir, laws = {}, options = {}) {
  return canon(ir, laws, options);
}

function normalizeNode(ir, ctx) {
  if (!ir || typeof ir !== 'object') return ir;

  if (ir.node === 'Seq') {
    const flattened = [];
    for (const child of ir.children ?? []) {
      const normalizedChild = normalizeNode(child, ctx);
      if (!normalizedChild) continue;
      if (normalizedChild.node === 'Seq') {
        flattened.push(...(normalizedChild.children ?? []));
      } else {
        flattened.push(normalizedChild);
      }
    }

    let current = flattened;
    while (true) {
      const { nodes, changed } = applySeqLaws(current, ctx);
      if (!changed) break;
      current = nodes;
    }

    if (current.length === 0) {
      return { ...ir, children: [] };
    }
    if (current.length === 1) {
      return current[0];
    }
    return { ...ir, children: current };
  }

  if (ir.node === 'Par') {
    return { ...ir, children: (ir.children ?? []).map((c) => normalizeNode(c, ctx)) };
  }

  if (ir.node === 'Region') {
    return { ...ir, children: (ir.children ?? []).map((c) => normalizeNode(c, ctx)) };
  }

  if (Array.isArray(ir.children)) {
    return { ...ir, children: ir.children.map((c) => normalizeNode(c, ctx)) };
  }

  return ir;
}

function applySeqLaws(children, ctx) {
  const collapsed = collapsePairs(children, ctx);
  const commuted = commuteEmitWithPure(collapsed.nodes, ctx);
  return {
    nodes: commuted.nodes,
    changed: collapsed.changed || commuted.changed
  };
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
        const inverse = ctx.inverseMap?.get(prevName);
        if (inverse && inverse === nodeName) {
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

  for (let i = 0; i < nodes.length - 1; i++) {
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
        i -= 2;
        if (i < -1) i = -1;
      }
    }
  }

  return { nodes, changed };
}

function primName(prim) {
  if (typeof prim !== 'string') return '';
  const parts = prim.split('/');
  const last = parts[parts.length - 1];
  if (!last) return '';
  const [name] = last.split('@');
  if (!name) return '';
  return name.toLowerCase();
}

function isPrim(node) {
  return node && node.node === 'Prim';
}

function buildLawContext(lawsSpec) {
  const entries = Array.isArray(lawsSpec?.laws) ? lawsSpec.laws : [];
  const idempotent = new Set();
  const commuteWithPure = new Set();
  const pure = new Set();
  const inverses = [];

  for (const law of entries) {
    const kind = typeof law?.kind === 'string' ? law.kind : '';
    const applies = law?.applies_to;

    if (kind === 'idempotent') {
      for (const id of toPrimList(applies)) {
        if (id) idempotent.add(id);
      }
    } else if (kind === 'inverse' || kind === 'eq') {
      for (const [left, right] of toPrimPairs(applies)) {
        if (left && right) {
          inverses.push([left, right]);
          inverses.push([right, left]);
        }
      }
    } else if (kind === 'commute-with-pure') {
      for (const id of toPrimList(applies)) {
        if (id && id !== 'pure') {
          commuteWithPure.add(id);
        }
      }
    } else if (kind === 'pure') {
      for (const id of toPrimList(applies)) {
        if (id && id !== 'pure') {
          pure.add(id);
        }
      }
    }
  }

  const inverseMap = new Map();
  for (const [left, right] of inverses) {
    inverseMap.set(left, right);
  }

  return { idempotent, inverses, commuteWithPure, pure, inverseMap };
}

function toPrimList(value) {
  const out = [];
  if (Array.isArray(value)) {
    for (const entry of value) {
      if (typeof entry === 'string') {
        const name = primName(entry);
        if (name) out.push(name);
      }
    }
  }
  return out;
}

function toPrimPairs(value) {
  const out = [];
  if (!Array.isArray(value)) return out;

  const allStrings = value.every((v) => typeof v === 'string');
  if (allStrings) {
    if (value.length >= 2) {
      const left = primName(value[0]);
      const right = primName(value[1]);
      out.push([left, right]);
    }
    return out;
  }

  for (const entry of value) {
    if (Array.isArray(entry) && entry.length >= 2) {
      const left = typeof entry[0] === 'string' ? primName(entry[0]) : '';
      const right = typeof entry[1] === 'string' ? primName(entry[1]) : '';
      out.push([left, right]);
    }
  }

  return out;
}

function isPurePrim(node, ctx) {
  if (!isPrim(node)) return false;
  if (Array.isArray(node.meta?.effects) && node.meta.effects.includes('Pure')) {
    return true;
  }
  if (Array.isArray(node.effects) && node.effects.includes('Pure')) {
    return true;
  }
  const name = primName(node.prim);
  if (!name) return false;
  if (ctx?.pure?.has(name)) return true;
  return KNOWN_PURE_PRIMS.has(name);
}
