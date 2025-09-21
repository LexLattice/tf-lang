const PRIM_PREFIX = 'Prim';
const PAR_PREFIX = 'Par';
const SEQ_PREFIX = 'Seq';
const WRITES_PREFIX = 'Writes';

export function emitAlloy(ir, options = {}) {
  const context = {
    nodeCounter: 0,
    writeCounter: 0,
    prims: [],
    pars: [],
    seqs: [],
    writes: [],
    names: new WeakMap()
  };

  processNode(ir, context);

  const scope = normalizeScope(options.scope);

  const prims = sortByName(context.prims);
  const pars = sortByName(context.pars);
  const seqs = sortByName(context.seqs);
  const writes = sortWrites(context.writes);

  const lines = [];
  lines.push('module tf_lang_l0');
  lines.push('open util/strings');
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
  lines.push('// Conflict: two writes to the same URI anywhere inside the Par\'s branches');
  lines.push('pred Conflicting[p: Par] {');
  lines.push(
    '  some disj a, b: Writes | a.node in p.*children && b.node in p.*children && a.uri = b.uri'
  );
  lines.push('}');
  lines.push('');
  lines.push('// Sanity: no conflicts is allowed model property');
  lines.push('pred NoConflict[p: Par] { not Conflicting[p] }');
  lines.push('');

  appendDeclarations(lines, { prims, pars, seqs, writes });
  appendFacts(lines, { prims, pars, seqs, writes });

  const scopeSuffix = scope ? ` for ${scope}` : '';
  lines.push(`run { some p: Par | Conflicting[p] }${scopeSuffix}`);
  lines.push(`run { all p: Par | NoConflict[p] }${scopeSuffix}`);

  return lines.join('\n') + '\n';
}

function appendDeclarations(lines, context) {
  const { prims, pars, seqs, writes } = context;
  if (prims.length > 0) {
    for (const prim of prims) {
      lines.push(`one sig ${prim.name} extends Prim {}`);
    }
    lines.push('');
  }
  if (pars.length > 0) {
    for (const par of pars) {
      lines.push(`one sig ${par.name} extends Par {}`);
    }
    lines.push('');
  }
  if (seqs.length > 0) {
    for (const seq of seqs) {
      lines.push(`one sig ${seq.name} extends Seq {}`);
    }
    lines.push('');
  }
  if (writes.length > 0) {
    for (const write of writes) {
      lines.push(`one sig ${write.name} extends Writes {}`);
    }
    lines.push('');
  }
}

function appendFacts(lines, context) {
  const { prims, pars, seqs, writes } = context;
  if (prims.length > 0) {
    lines.push('fact PrimIds {');
    for (const prim of prims) {
      lines.push(`  ${prim.name}.id = ${stringLiteral(prim.id)}`);
    }
    lines.push('}');
    lines.push('');
  }

  if (pars.length > 0) {
    lines.push('fact ParChildren {');
    for (const par of pars) {
      const expr = formatSetExpression(par.children);
      lines.push(`  ${par.name}.children = ${expr}`);
    }
    lines.push('}');
    lines.push('');
  }

  if (seqs.length > 0) {
    lines.push('fact SeqChildren {');
    for (const seq of seqs) {
      const expr = formatSeqExpression(seq.children);
      lines.push(`  ${seq.name}.children = ${expr}`);
    }
    lines.push('}');
    lines.push('');
  }

  if (writes.length > 0) {
    lines.push('fact WriteLinks {');
    for (const write of writes) {
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
  const sorted = [...children].sort();
  return sorted.join(' + ');
}

function formatSeqExpression(children) {
  if (!children || children.length === 0) {
    return 'none';
  }
  return children.map((child, index) => `${index} -> ${child}`).join(' + ');
}

function processNode(node, context) {
  if (!node || typeof node !== 'object') {
    return null;
  }
  if (context.names.has(node)) {
    return context.names.get(node);
  }

  const kind = typeof node.node === 'string' ? node.node : inferNodeKind(node);
  if (kind === 'Prim') {
    return registerPrim(node, context);
  }
  if (kind === 'Par') {
    return registerPar(node, context);
  }
  if (kind === 'Seq') {
    return registerSeq(node, context);
  }
  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      processNode(child, context);
    }
  }
  return null;
}

function registerPrim(node, context) {
  const ordinal = context.nodeCounter++;
  const name = `${PRIM_PREFIX}${ordinal}`;
  const primName = typeof node.prim === 'string' ? node.prim : null;
  const explicitId = typeof node.id === 'string' && node.id.length > 0 ? node.id : null;
  const id = explicitId ?? (primName ? `${primName}#${ordinal}` : name);

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
  const ordinal = context.nodeCounter++;
  const name = `${PAR_PREFIX}${ordinal}`;
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
  const ordinal = context.nodeCounter++;
  const name = `${SEQ_PREFIX}${ordinal}`;
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
  const index = context.writeCounter++;
  const name = `${WRITES_PREFIX}${index}`;
  context.writes.push({ name, node: nodeName, uri });
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

function sortByName(entries) {
  return [...entries].sort((a, b) => a.name.localeCompare(b.name));
}

function sortWrites(entries) {
  return [...entries].sort((a, b) => {
    const nodeCmp = a.node.localeCompare(b.node);
    if (nodeCmp !== 0) {
      return nodeCmp;
    }
    const uriCmp = a.uri.localeCompare(b.uri);
    if (uriCmp !== 0) {
      return uriCmp;
    }
    return a.name.localeCompare(b.name);
  });
}

function inferNodeKind(node) {
  if (Array.isArray(node?.children)) {
    return 'Seq';
  }
  return null;
}

function normalizeScope(scope) {
  if (typeof scope === 'string' && scope.trim().length > 0) {
    const parsed = Number.parseInt(scope, 10);
    if (Number.isFinite(parsed)) {
      scope = parsed;
    }
  }
  if (typeof scope !== 'number') {
    return null;
  }
  if (!Number.isFinite(scope)) {
    return null;
  }
  const integer = Math.trunc(scope);
  return integer > 0 ? integer : null;
}
