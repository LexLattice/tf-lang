const HEADER = [
  'module tf_lang_l0',
  '',
  'open util/seq[Node]',
  '',
  'abstract sig Node {}',
  'abstract sig Prim extends Node { id: one String }',
  '',
  'sig Par extends Node { children: set Node }',
  'sig Seq extends Node { children: seq Node }',
  '',
  'one sig URI extends String {}',
  'sig Writes { node: one Prim, uri: one String }',
  '',
  'pred Conflicting[p: Par] {',
  '  some disj a, b: Writes | a.node in p.children && b.node in p.children && a.uri = b.uri',
  '}',
  '',
  'pred NoConflict[p: Par] { not Conflicting[p] }',
  ''
];

export function emitAlloy(ir) {
  const state = {
    counters: { Prim: 0, Par: 0, Seq: 0, Writes: 0 },
    prims: [],
    pars: [],
    seqs: [],
    writes: []
  };

  traverse(ir, state);

  const lines = [...HEADER];

  const nodeDecls = [];
  for (const prim of state.prims) {
    nodeDecls.push(`one sig ${prim.name} extends Prim {}`);
  }
  for (const par of state.pars) {
    nodeDecls.push(`one sig ${par.name} extends Par {}`);
  }
  for (const seq of state.seqs) {
    nodeDecls.push(`one sig ${seq.name} extends Seq {}`);
  }
  for (const write of state.writes) {
    nodeDecls.push(`one sig ${write.name} extends Writes {}`);
  }
  if (nodeDecls.length > 0) {
    lines.push(...nodeDecls, '');
  }

  const primIdFacts = state.prims.map((prim) => `${prim.name}.id = ${prim.id}`);
  addFact(lines, 'PrimIds', primIdFacts);

  for (const par of state.pars) {
    const factLines = buildParChildrenFact(par);
    addFact(lines, `${par.name}_Children`, factLines);
  }

  for (const seq of state.seqs) {
    const factLines = buildSeqChildrenFact(seq);
    addFact(lines, `${seq.name}_Children`, factLines);
  }

  const writeFacts = [];
  for (const write of state.writes) {
    writeFacts.push(`${write.name}.node = ${write.node}`);
    writeFacts.push(`${write.name}.uri = ${write.uri}`);
  }
  addFact(lines, 'WritesAssignments', writeFacts);

  lines.push('run { some p: Par | Conflicting[p] } for 5');
  lines.push('run { all p: Par | NoConflict[p] } for 5');

  return lines.join('\n') + '\n';
}

function traverse(node, state) {
  if (!node || typeof node !== 'object') {
    return null;
  }

  let record = null;
  if (node.node === 'Prim') {
    record = createPrim(node, state);
  } else if (node.node === 'Par') {
    record = createPar(state);
  } else if (node.node === 'Seq') {
    record = createSeq(state);
  }

  const children = [];
  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      const childRecord = traverse(child, state);
      if (childRecord) {
        children.push(childRecord);
      }
    }
  }

  if (record) {
    if (record.type === 'Par') {
      record.children = children;
    } else if (record.type === 'Seq') {
      record.children = children;
    }
  }

  return record;
}

function createPrim(node, state) {
  const name = `Prim${state.counters.Prim++}`;
  const idValue = selectPrimId(node, name);
  const prim = { type: 'Prim', name, id: stringLiteral(idValue) };
  state.prims.push(prim);

  const uris = extractWriteUris(node);
  for (const uri of uris) {
    const writeName = `Write${state.counters.Writes++}`;
    state.writes.push({ name: writeName, node: name, uri: stringLiteral(uri) });
  }

  return prim;
}

function createPar(state) {
  const name = `Par${state.counters.Par++}`;
  const par = { type: 'Par', name, children: [] };
  state.pars.push(par);
  return par;
}

function createSeq(state) {
  const name = `Seq${state.counters.Seq++}`;
  const seq = { type: 'Seq', name, children: [] };
  state.seqs.push(seq);
  return seq;
}

function selectPrimId(node, fallback) {
  if (typeof node.id === 'string' && node.id.length > 0) {
    return node.id;
  }
  if (typeof node.prim === 'string' && node.prim.length > 0) {
    return node.prim;
  }
  return fallback;
}

function extractWriteUris(node) {
  const fromWrites = Array.isArray(node.writes) ? node.writes : [];
  const collected = [];
  for (const entry of fromWrites) {
    const uri = normalizeUri(entry);
    if (typeof uri === 'string' && uri.length > 0) {
      collected.push(uri);
    }
  }
  if (collected.length > 0) {
    return dedupe(collected);
  }
  const fallbackUri = typeof node?.args?.uri === 'string' ? node.args.uri : null;
  if (fallbackUri && fallbackUri.length > 0) {
    return [fallbackUri];
  }
  return [];
}

function normalizeUri(entry) {
  if (typeof entry === 'string') {
    return entry;
  }
  if (entry && typeof entry === 'object' && typeof entry.uri === 'string') {
    return entry.uri;
  }
  return null;
}

function dedupe(values) {
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

function buildParChildrenFact(par) {
  if (!par.children || par.children.length === 0) {
    return [`no ${par.name}.children`];
  }
  const parts = par.children.map((child) => child.name);
  return [`${par.name}.children = ${parts.join(' + ')}`];
}

function buildSeqChildrenFact(seq) {
  if (!seq.children || seq.children.length === 0) {
    return [`no ${seq.name}.children`];
  }
  const facts = [`#${seq.name}.children = ${seq.children.length}`];
  seq.children.forEach((child, index) => {
    facts.push(`${seq.name}.children[${index}] = ${child.name}`);
  });
  return facts;
}

function addFact(lines, name, predicates) {
  if (!predicates || predicates.length === 0) {
    return;
  }
  lines.push(`fact ${name} {`);
  predicates.forEach((predicate, index) => {
    const suffix = index === predicates.length - 1 ? '' : ' &&';
    lines.push(`  ${predicate}${suffix}`);
  });
  lines.push('}', '');
}

function stringLiteral(value) {
  const s = typeof value === 'string' ? value : '';
  const escaped = s.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
  return `"${escaped}"`;
}
