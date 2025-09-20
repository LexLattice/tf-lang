import { unionEffects } from './lattice.mjs';
import { conflict } from './footprints.mjs';

export function checkIR(ir, catalog) {
  const verdict = walk(ir, catalog);
  return verdict;
}

function walk(node, catalog) {
  if (node.node === 'Prim') {
    const prim = lookup(node.prim, catalog);
    return { ok: true, effects: prim.effects||[], reads: prim.reads||[], writes: prim.writes||[], reasons: [] };
  }
  if (node.node === 'Seq') {
    let acc = { ok: true, effects: [], reads: [], writes: [], reasons: [] };
    for (const c of node.children||[]) {
      const v = walk(c, catalog);
      acc.ok = acc.ok && v.ok;
      acc.effects = unionEffects(acc.effects, v.effects);
      acc.reads = [...acc.reads, ...(v.reads||[])];
      acc.writes = [...acc.writes, ...(v.writes||[])];
      acc.reasons.push(...v.reasons);
    }
    return acc;
  }
  if (node.node === 'Par') {
    const vs = (node.children||[]).map(c => walk(c, catalog));
    let ok = vs.every(v => v.ok);
    // pairwise conflict check on writes
    for (let i=0;i<vs.length;i++) for (let j=i+1;j<vs.length;j++) {
      if (conflict(vs[i].writes, vs[j].writes)) { ok = false; }
    }
    return {
      ok,
      effects: vs.reduce((e,v)=>unionEffects(e,v.effects), []),
      reads: vs.flatMap(v=>v.reads||[]),
      writes: vs.flatMap(v=>v.writes||[]),
      reasons: ok?[]:["Par conflict: overlapping writes detected"]
    };
  }
  return { ok: true, effects: [], reads: [], writes: [], reasons: [] };
}

function lookup(primName, catalog) {
  // match by trailing name token
  const name = primName.toLowerCase();
  const hit = (catalog.primitives||[]).find(p=>p.name===name || p.id.endsWith('/'+name+'@1'));
  return hit || { id: primName, name: primName, effects: [], reads: [], writes: [] };
}
