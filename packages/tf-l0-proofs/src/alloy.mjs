const PRIM_PREFIX = 'Prim';
const PAR_PREFIX = 'Par';
const SEQ_PREFIX = 'Seq';
const WRITES_PREFIX = 'Writes';

export function emitAlloy(ir) {
  const context = {
    prims: [],
    pars: [],
    seqs: [],
    writes: [],
    counters: new Map(),
    names: new WeakMap()
  };

  processNode(ir, context);

  const lines = [];
  lines.push('module tf_lang_l0');
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

  appendDeclarations(lines, context);
  appendFacts(lines, context);

  lines.push('run { some p: Par | Conflicting[p] } for 5');
  lines.push('run { all p: Par | NoConflict[p] } for 5');

  return lines.join('\n') + '\n';
}

function appendDeclarations(lines, context) {
  if (context.prims.length > 0) {
    for (const prim of context.prims) {
      lines.push(`one sig ${prim.name} extends Prim {}`);
    }
    lines.push('');
  }
  if (context.pars.length > 0) {
    for (const par of context.pars) {
      lines.push(`one sig ${par.name} extends Par {}`);
    }
    lines.push('');
  }
  if (context.seqs.length > 0) {
    for (const seq of context.seqs) {
      lines.push(`one sig ${seq.name} extends Seq {}`);
    }
    lines.push('');
  }
  if (context.writes.length > 0) {
    for (const write of context.writes) {
      lines.push(`one sig ${write.name} extends Writes {}`);
    }
    lines.push('');
  }
}

function appendFacts(lines, context) {
  if (context.prims.length > 0) {
    lines.push('fact PrimIds {');
    for (const prim of context.prims) {
      lines.push(`  ${prim.name}.id = ${stringLiteral(prim.id)}`);
    }
    lines.push('}');
    lines.push('');
  }

  if (context.pars.length > 0) {
    lines.push('fact ParChildren {');
    for (const par of context.pars) {
      const expr = formatSetExpression(par.children);
      lines.push(`  ${par.name}.children = ${expr}`);
    }
    lines.push('}');
    lines.push('');
  }

  if (context.seqs.length > 0) {
    lines.push('fact SeqChildren {');
    for (const seq of context.seqs) {
      const expr = formatSeqExpression(seq.children);
      lines.push(`  ${seq.name}.children = ${expr}`);
    }
    lines.push('}');
    lines.push('');
  }

  if (context.writes.length > 0) {
    lines.push('fact WriteLinks {');
    for (const write of context.writes) {
      lines.push(`  ${write.name}.node = ${write.node}`);
      lines.push(`  ${write.name}.uri = ${stringLiteral(write.uri)}`);
    }
    lines.push('}');
    lines.push('');
  }
}

function formatSetExpression(children) {
  if (!children || children.length === 0) {
    return 'none';
  }
  if (children.length === 1) {
    return children[0];
  }
  return children.join(' + ');
}

function formatSeqExpression(children) {
  if (!children || children.length === 0) {
    return 'none';
  }
  const pairs = children.map((child, index) => `${index} -> ${child}`);
  return pairs.join(' + ');
}

function processNode(node, context) {
  if (!node || typeof node !== 'object') {
    return null;
  }
  if (context.names.has(node)) {
    return context.names.get(node);
  }
  const type = typeof node.node === 'string' ? node.node : '';
  if (type === 'Prim') {
    return registerPrim(node, context);
  }
  if (type === 'Par') {
    return registerPar(node, context);
  }
  if (type === 'Seq' || Array.isArray(node.children)) {
    return registerSeq(node, context);
  }
  return null;
}

function registerPrim(node, context) {
  const index = nextIndex(context, PRIM_PREFIX);
  const name = `${PRIM_PREFIX}${index}`;
  const primName = typeof node.prim === 'string' ? node.prim : null;
  const id = typeof node.id === 'string' && node.id.length > 0
    ? node.id
    : primName
    ? `${primName}#${index}`
    : name;
  const entry = { type: 'Prim', name, id };
  context.prims.push(entry);
  context.names.set(node, entry);

  const uris = collectWriteUris(node);
  for (const uri of uris) {
    registerWrite(entry.name, uri, context);
  }
  return entry;
}

function registerPar(node, context) {
  const index = nextIndex(context, PAR_PREFIX);
  const name = `${PAR_PREFIX}${index}`;
  const children = [];
  for (const child of node.children || []) {
    const result = processNode(child, context);
    if (result) {
      children.push(result.name);
    }
  }
  const entry = { type: 'Par', name, children };
  context.pars.push(entry);
  context.names.set(node, entry);
  return entry;
}

function registerSeq(node, context) {
  const index = nextIndex(context, SEQ_PREFIX);
  const name = `${SEQ_PREFIX}${index}`;
  const children = [];
  for (const child of node.children || []) {
    const result = processNode(child, context);
    if (result) {
      children.push(result.name);
    }
  }
  const entry = { type: 'Seq', name, children };
  context.seqs.push(entry);
  context.names.set(node, entry);
  return entry;
}

function registerWrite(nodeName, uri, context) {
  const index = nextIndex(context, WRITES_PREFIX);
  const name = `${WRITES_PREFIX}${index}`;
  context.writes.push({ name, node: nodeName, uri });
}

function nextIndex(context, prefix) {
  const current = context.counters.get(prefix) ?? 0;
  context.counters.set(prefix, current + 1);
  return current;
}

function collectWriteUris(node) {
  if (!node || typeof node !== 'object') {
    return [];
  }
  const urisFromWrites = collectUrisFromWrites(node);
  if (urisFromWrites.length > 0) {
    return urisFromWrites;
  }
  if (!isWritePrimName(node.prim)) {
    return [];
  }
  const fromArgs = selectUriFromArgs(node.args);
  return fromArgs ? [fromArgs] : [];
}

function collectUrisFromWrites(node) {
  if (!Array.isArray(node.writes) || node.writes.length === 0) {
    return [];
  }
  const seen = new Set();
  const result = [];
  for (const entry of node.writes) {
    const uri = concretizeUri(entry);
    if (!uri || seen.has(uri)) {
      continue;
    }
    seen.add(uri);
    result.push(uri);
  }
  result.sort();
  return result;
}

function concretizeUri(entry) {
  if (typeof entry === 'string') {
    return isConcreteUri(entry) ? entry : null;
  }
  if (entry && typeof entry === 'object' && typeof entry.uri === 'string') {
    return isConcreteUri(entry.uri) ? entry.uri : null;
  }
  return null;
}

function selectUriFromArgs(args = {}) {
  if (!args || typeof args !== 'object') {
    return null;
  }
  const keys = ['uri', 'resource_uri', 'bucket_uri'];
  for (const key of keys) {
    const value = args[key];
    if (isConcreteUri(value)) {
      return value;
    }
  }
  return null;
}

function isConcreteUri(uri) {
  return typeof uri === 'string' && uri.length > 0 && uri !== 'res://unknown' && !/[<>]/.test(uri);
}

function isWritePrimName(name) {
  if (typeof name !== 'string') {
    return false;
  }
  const lower = name.toLowerCase();
  return lower.includes('write') || lower.includes('put') || lower.includes('update') || lower.includes('set');
}

function stringLiteral(value) {
  const s = typeof value === 'string' ? value : '';
  const escaped = s.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
  return `"${escaped}"`;
}
