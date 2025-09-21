export function emitAlloy(ir) {
  const ctx = {
    prims: [],
    pars: [],
    seqs: [],
    writes: [],
    counters: {
      Prim: 0,
      Par: 0,
      Seq: 0,
      Writes: 0,
    },
  };

  visitNode(ir, ctx);

  const lines = [];
  lines.push('module tf_lang_l0');
  lines.push('');
  lines.push('open util/seq[Node]');
  lines.push('');
  lines.push('abstract sig Node {}');
  lines.push('abstract sig Prim extends Node { id: one String }');
  lines.push('');
  lines.push('sig Par extends Node { children: set Node }');
  lines.push('sig Seq extends Node { children: seq Node }');
  lines.push('');
  lines.push('// Writes footprint (abstracted to URIs as Strings)');
  lines.push('one sig URI extends String {}');
  lines.push('sig Writes { node: one Prim, uri: one String }');
  lines.push('');
  lines.push('// Conflict: two writes to the same URI under the same Par');
  lines.push('pred Conflicting[p: Par] {');
  lines.push(
    '  some disj a, b: Writes | a.node in p.children && b.node in p.children && a.uri = b.uri'
  );
  lines.push('}');
  lines.push('');
  lines.push('// Sanity: no conflicts is allowed model property');
  lines.push('pred NoConflict[p: Par] { not Conflicting[p] }');
  lines.push('');

  for (const prim of ctx.prims) {
    lines.push(`one sig ${prim.name} extends Prim {}`);
  }
  for (const par of ctx.pars) {
    lines.push(`one sig ${par.name} extends Par {}`);
  }
  for (const seq of ctx.seqs) {
    lines.push(`one sig ${seq.name} extends Seq {}`);
  }
  for (const write of ctx.writes) {
    lines.push(`one sig ${write.name} extends Writes {}`);
  }

  const facts = [];
  for (const prim of ctx.prims) {
    facts.push(`  ${prim.name}.id = ${stringLiteral(prim.id)}`);
  }
  for (const par of ctx.pars) {
    facts.push(`  ${par.name}.children = ${setExpression(par.children)}`);
  }
  for (const seq of ctx.seqs) {
    facts.push(`  ${seq.name}.children = ${sequenceExpression(seq.children)}`);
  }
  for (const write of ctx.writes) {
    facts.push(
      `  ${write.name}.node = ${write.prim} && ${write.name}.uri = ${stringLiteral(write.uri)}`
    );
  }

  if (facts.length > 0) {
    lines.push('');
    lines.push('fact {');
    lines.push(facts.join('\n'));
    lines.push('}');
  }

  lines.push('');
  lines.push('run { some p: Par | Conflicting[p] } for 5');
  lines.push('run { all p: Par | NoConflict[p] } for 5');

  return lines.join('\n') + '\n';
}

function visitNode(node, ctx) {
  if (!node || typeof node !== 'object') {
    return null;
  }

  switch (node.node) {
    case 'Prim':
      return registerPrim(node, ctx);
    case 'Par':
      return registerPar(node, ctx);
    case 'Seq':
      return registerSeq(node, ctx);
    default:
      break;
  }

  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      visitNode(child, ctx);
    }
  }

  return null;
}

function registerPrim(node, ctx) {
  const name = `Prim${ctx.counters.Prim++}`;
  const id = primIdentifier(node, name);
  const record = { name, id };
  ctx.prims.push(record);

  const uris = extractWriteUris(node);
  for (const uri of uris) {
    const writeName = `Writes${ctx.counters.Writes++}`;
    ctx.writes.push({ name: writeName, prim: name, uri });
  }

  return name;
}

function registerPar(node, ctx) {
  const name = `Par${ctx.counters.Par++}`;
  const record = { name, children: [] };
  ctx.pars.push(record);

  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      const childName = visitNode(child, ctx);
      if (childName) {
        record.children.push(childName);
      }
    }
  }

  record.children = dedupePreserveOrder(record.children);
  return name;
}

function registerSeq(node, ctx) {
  const name = `Seq${ctx.counters.Seq++}`;
  const record = { name, children: [] };
  ctx.seqs.push(record);

  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      const childName = visitNode(child, ctx);
      if (childName) {
        record.children.push(childName);
      }
    }
  }

  return name;
}

function primIdentifier(node, fallback) {
  if (typeof node?.id === 'string' && node.id.length > 0) {
    return node.id;
  }
  if (typeof node?.prim === 'string' && node.prim.length > 0) {
    return node.prim;
  }
  return fallback;
}

function extractWriteUris(node) {
  const uris = [];
  if (Array.isArray(node?.writes) && node.writes.length > 0) {
    for (const entry of node.writes) {
      const uri = entry?.uri;
      if (typeof uri === 'string' && uri.length > 0) {
        uris.push(uri);
      }
    }
  }

  if (uris.length === 0) {
    const fallback = node?.args?.uri;
    if (typeof fallback === 'string' && fallback.length > 0) {
      uris.push(fallback);
    }
  }

  return Array.from(new Set(uris)).sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
}

function setExpression(children) {
  if (!Array.isArray(children) || children.length === 0) {
    return 'none';
  }
  return children.join(' + ');
}

function sequenceExpression(children) {
  if (!Array.isArray(children) || children.length === 0) {
    return 'none';
  }
  return children
    .map((child, index) => `${index} -> ${child}`)
    .join(' + ');
}

function stringLiteral(value) {
  const raw = typeof value === 'string' ? value : '';
  const escaped = raw.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
  return `"${escaped}"`;
}

function dedupePreserveOrder(values = []) {
  const seen = new Set();
  const result = [];
  for (const value of values) {
    if (!seen.has(value)) {
      seen.add(value);
      result.push(value);
    }
  }
  return result;
}
