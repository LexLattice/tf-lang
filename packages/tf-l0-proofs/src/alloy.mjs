const BASE_MODULE = `module tf_lang_l0

abstract sig Node {}
abstract sig Prim extends Node { id: one String }

sig Par extends Node { children: set Node }
sig Seq extends Node { children: seq Node }

// Writes footprint (abstracted to URIs as Strings)
one sig URI extends String {}
sig Writes { node: one Prim, uri: one String }

// Conflict: two writes to the same URI under the same Par
pred Conflicting[p: Par] {
  some disj a, b: Writes | a.node in p.children && b.node in p.children && a.uri = b.uri
}

// Sanity: no conflicts is allowed model property
pred NoConflict[p: Par] { not Conflicting[p] }
`;

export function emitAlloy(ir) {
  const ctx = createContext();
  collectNodes(ir, ctx);
  const lines = [BASE_MODULE.trimEnd()];

  if (ctx.nodes.length > 0) {
    lines.push('');
    for (const record of ctx.nodes) {
      lines.push(`one sig ${record.name} extends ${record.type} {}`);
    }
  }

  if (ctx.writes.length > 0) {
    lines.push('');
    for (const write of ctx.writes) {
      lines.push(`one sig ${write.name} extends Writes {}`);
    }
  }

  const facts = buildFacts(ctx);
  if (facts.length > 0) {
    lines.push('');
    lines.push(...facts);
  }

  lines.push('');
  lines.push('run { some p: Par | Conflicting[p] } for 5');
  lines.push('run { all p: Par | NoConflict[p] } for 5');

  lines.push('');
  return lines.join('\n');
}

function createContext() {
  return {
    counters: { Prim: 0, Par: 0, Seq: 0, Writes: 0 },
    nodes: [],
    writes: [],
    map: new Map()
  };
}

function collectNodes(node, ctx) {
  if (!node || typeof node !== 'object') {
    return null;
  }
  if (ctx.map.has(node)) {
    return ctx.map.get(node);
  }
  const type = classifyNode(node);
  if (!type) {
    if (Array.isArray(node.children)) {
      for (const child of node.children) {
        collectNodes(child, ctx);
      }
    }
    return null;
  }
  const name = `${type}${ctx.counters[type]++}`;
  const record = initializeRecord(type, name, node, ctx);
  ctx.map.set(node, record);
  ctx.nodes.push(record);
  if (type === 'Prim') {
    populatePrim(record, node, ctx);
  } else {
    const children = Array.isArray(node.children) ? node.children : [];
    for (const child of children) {
      const childRecord = collectNodes(child, ctx);
      if (childRecord) {
        record.children.push(childRecord.name);
      }
    }
  }
  return record;
}

function classifyNode(node) {
  if (!node || typeof node !== 'object') {
    return null;
  }
  switch (node.node) {
    case 'Prim':
      return 'Prim';
    case 'Par':
      return 'Par';
    case 'Seq':
    case 'Region':
      return 'Seq';
    default:
      return null;
  }
}

function initializeRecord(type, name, node, ctx) {
  if (type === 'Prim') {
    return {
      type,
      name,
      id: typeof node.prim === 'string' && node.prim.length > 0 ? node.prim : 'unknown-prim',
      children: [],
      writes: []
    };
  }
  return {
    type,
    name,
    children: []
  };
}

function populatePrim(record, node, ctx) {
  const uris = extractUris(node);
  record.writes = uris;
  for (const uri of uris) {
    const writeName = `Write${ctx.counters.Writes++}`;
    ctx.writes.push({ name: writeName, node: record.name, uri });
  }
}

function extractUris(node) {
  const seen = new Set();
  const uris = [];
  if (Array.isArray(node.writes)) {
    for (const entry of node.writes) {
      const uri = extractUriValue(entry);
      if (isConcreteUri(uri) && !seen.has(uri)) {
        seen.add(uri);
        uris.push(uri);
      }
    }
  }
  if (uris.length === 0) {
    const fallback = typeof node?.args?.uri === 'string' ? node.args.uri : null;
    if (isConcreteUri(fallback) && !seen.has(fallback)) {
      seen.add(fallback);
      uris.push(fallback);
    }
  }
  return uris;
}

function extractUriValue(entry) {
  if (typeof entry === 'string') {
    return entry;
  }
  if (entry && typeof entry === 'object' && typeof entry.uri === 'string') {
    return entry.uri;
  }
  return null;
}

function isConcreteUri(uri) {
  return typeof uri === 'string' && uri.length > 0 && uri !== 'res://unknown' && !/[<>]/.test(uri);
}

function buildFacts(ctx) {
  const lines = [];
  for (const record of ctx.nodes) {
    if (record.type === 'Prim') {
      lines.push(`fact ${record.name}_id { ${record.name}.id = ${stringLiteral(record.id)} }`);
    }
  }
  for (const record of ctx.nodes) {
    if (record.type === 'Par') {
      lines.push(...renderParFact(record));
    } else if (record.type === 'Seq') {
      lines.push(...renderSeqFact(record));
    }
  }
  for (const write of ctx.writes) {
    lines.push(
      `fact ${write.name}_binding { ${write.name}.node = ${write.node} && ${write.name}.uri = ${stringLiteral(write.uri)} }`
    );
  }
  return lines;
}

function renderParFact(record) {
  const childrenExpr = record.children.length === 0 ? 'none' : record.children.join(' + ');
  return [`fact ${record.name}_children { ${record.name}.children = ${childrenExpr} }`];
}

function renderSeqFact(record) {
  const sizeLine = `  #${record.name}.children = ${record.children.length}`;
  if (record.children.length === 0) {
    return [`fact ${record.name}_children {`, `${sizeLine}`, `}`];
  }
  const lines = [`fact ${record.name}_children {`, sizeLine];
  record.children.forEach((child, index) => {
    lines.push(`  && ${record.name}.children[${index}] = ${child}`);
  });
  lines.push('}');
  return lines;
}

function stringLiteral(value) {
  const s = typeof value === 'string' ? value : '';
  const escaped = s.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
  return `"${escaped}"`;
}
