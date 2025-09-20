// Minimal normalizer: flattens adjacent Seq and dedups consecutive idempotent Prim by name.
export function normalize(ir, laws={}) {
  if (!ir || typeof ir !== 'object') return ir;
  if (ir.node === 'Seq') {
    const flat = [];
    for (const c of ir.children || []) {
      const n = normalize(c, laws);
      if (n && n.node === 'Seq') flat.push(...n.children);
      else flat.push(n);
    }
    return { ...ir, children: dedup(flat, laws) };
  }
  if (ir.node === 'Par') {
    return { ...ir, children: (ir.children||[]).map(c => normalize(c, laws)) };
  }
  return ir;
}

function dedup(children, laws) {
  // idempotent consecutive Prim: e.g., hash ∘ hash => hash
  const out = [];
  for (const c of children) {
    const prev = out[out.length-1];
    if (prev && prev.node==='Prim' && c.node==='Prim' && prev.prim === c.prim && isIdempotent(prev.prim, laws)) {
      continue;
    }
    out.push(c);
  }
  return out;
}

function isIdempotent(prim, laws) {
  const items = (laws?.laws)||[];
  return items.some(l => l.kind==='idempotent' && l.applies_to && l.applies_to.find(id=>prim.includes(id.split('/')[1].split('@')[0])));
}
