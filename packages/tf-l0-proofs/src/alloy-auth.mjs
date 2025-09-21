const REGION_PREFIX = 'Region';
const PRIM_PREFIX = 'Prim';
const SCOPE_PREFIX = 'Scope';

export function emitAlloyAuth(ir, options = {}) {
  const context = {
    regions: [],
    prims: [],
    scopeEntries: [],
    scopeMap: new Map(),
    regionCounter: 0,
    primCounter: 0,
    nodeNames: new WeakMap(),
    primIndex: normalizePrimIndex(options.primIndex),
  };

  traverse(ir, [], context);

  const lines = [];
  lines.push('module tf_lang_authorize');
  lines.push('');
  lines.push('open util/ordering[Node]');
  lines.push('');
  lines.push('sig Node {}');
  lines.push('sig Region extends Node { scopes: set Scope, children: set Node }');
  lines.push('sig Prim extends Node { primId: one String, scopeNeed: set Scope }');
  lines.push('sig Scope {}');
  lines.push('');
  lines.push('pred Dominates[r:Region, n:Node] { n in r.*children }');
  lines.push('pred Covered[n:Prim] { some r:Region | Dominates[r, n] and some (r.scopes & n.scopeNeed) }');
  lines.push('pred MissingAuth { some n:Prim | some n.scopeNeed and not Covered[n] }');
  lines.push('');

  appendScopeDeclarations(lines, context.scopeEntries);
  appendRegionDeclarations(lines, context.regions);
  appendPrimDeclarations(lines, context.prims);
  appendRegionFacts(lines, context.regions);
  appendPrimFacts(lines, context.prims);

  lines.push('run { MissingAuth }');
  lines.push('run { not MissingAuth }');

  return lines.join('\n') + '\n';
}

function normalizePrimIndex(value) {
  if (value instanceof Map) {
    return value;
  }
  if (!value || typeof value !== 'object') {
    return new Map();
  }
  const map = new Map();
  for (const [key, entry] of Object.entries(value)) {
    if (!entry || typeof entry !== 'object') {
      continue;
    }
    const { id, scopes } = entry;
    if (typeof key === 'string') {
      map.set(key, {
        id: typeof id === 'string' && id.length > 0 ? id : null,
        scopes: Array.isArray(scopes) ? scopes.filter(isNonEmptyString) : [],
      });
    }
  }
  return map;
}

function traverse(node, regionStack, context) {
  if (!node || typeof node !== 'object') {
    return;
  }
  if (context.nodeNames.has(node)) {
    return;
  }

  if (node.node === 'Region' && node.kind === 'Authorize') {
    const region = registerRegion(node, context);
    if (regionStack.length > 0) {
      const parent = regionStack[regionStack.length - 1];
      parent.children.add(region.name);
    }
    regionStack.push(region);
    for (const child of node.children || []) {
      traverse(child, regionStack, context);
    }
    regionStack.pop();
    return;
  }

  if (node.node === 'Prim') {
    const prim = registerPrim(node, context);
    if (regionStack.length > 0) {
      const parent = regionStack[regionStack.length - 1];
      parent.children.add(prim.name);
    }
  }

  if (Array.isArray(node.children)) {
    for (const child of node.children) {
      traverse(child, regionStack, context);
    }
  }
}

function registerRegion(node, context) {
  if (context.nodeNames.has(node)) {
    return context.nodeNames.get(node);
  }
  const name = `${REGION_PREFIX}${context.regionCounter++}`;
  const scopes = collectRegionScopes(node, context);
  const entry = { name, scopes, children: new Set() };
  context.nodeNames.set(node, entry);
  context.regions.push(entry);
  return entry;
}

function collectRegionScopes(node, context) {
  const scopes = new Set();
  const raw = node?.attrs?.scope;
  if (typeof raw === 'string') {
    for (const scope of splitScopes(raw)) {
      const atom = internScope(scope, context);
      if (atom) {
        scopes.add(atom);
      }
    }
  }
  return scopes;
}

function registerPrim(node, context) {
  if (context.nodeNames.has(node)) {
    return context.nodeNames.get(node);
  }
  const name = `${PRIM_PREFIX}${context.primCounter++}`;
  const info = lookupPrimInfo(node, context.primIndex);
  const scopeNeeds = new Set();
  for (const scope of info.scopes) {
    const atom = internScope(scope, context);
    if (atom) {
      scopeNeeds.add(atom);
    }
  }
  const entry = {
    name,
    primId: info.id ?? inferPrimId(node),
    scopeNeeds,
  };
  context.nodeNames.set(node, entry);
  context.prims.push(entry);
  return entry;
}

function lookupPrimInfo(node, primIndex) {
  const primName = typeof node?.prim === 'string' ? node.prim.toLowerCase() : '';
  return primIndex.get(primName) ?? { id: null, scopes: [] };
}

function inferPrimId(node) {
  if (typeof node?.prim === 'string' && node.prim.length > 0) {
    return node.prim;
  }
  return 'unknown-prim';
}

function splitScopes(value) {
  return value
    .split(',')
    .map((entry) => entry.trim())
    .filter(isNonEmptyString);
}

function internScope(scope, context) {
  if (!isNonEmptyString(scope)) {
    return null;
  }
  if (context.scopeMap.has(scope)) {
    return context.scopeMap.get(scope).name;
  }
  const name = makeScopeAtom(scope, context.scopeEntries);
  const entry = { label: scope, name };
  context.scopeEntries.push(entry);
  context.scopeMap.set(scope, entry);
  return name;
}

function makeScopeAtom(scope, entries) {
  const base = `${SCOPE_PREFIX}_${sanitize(scope)}`;
  let candidate = base;
  let index = 1;
  while (entries.some((entry) => entry.name === candidate)) {
    candidate = `${base}_${index++}`;
  }
  return candidate;
}

function sanitize(text) {
  let result = text.replace(/[^A-Za-z0-9_]/g, '_');
  if (!/[A-Za-z_]/.test(result.charAt(0))) {
    result = `S_${result}`;
  }
  return result;
}

function appendScopeDeclarations(lines, scopes) {
  if (scopes.length === 0) {
    return;
  }
  const ordered = [...scopes].sort((a, b) => a.name.localeCompare(b.name));
  for (const scope of ordered) {
    lines.push(`one sig ${scope.name} extends Scope {}`);
  }
  lines.push('');
}

function appendRegionDeclarations(lines, regions) {
  if (regions.length === 0) {
    return;
  }
  const ordered = [...regions].sort((a, b) => a.name.localeCompare(b.name));
  for (const region of ordered) {
    lines.push(`one sig ${region.name} extends Region {}`);
  }
  lines.push('');
}

function appendPrimDeclarations(lines, prims) {
  if (prims.length === 0) {
    return;
  }
  const ordered = [...prims].sort((a, b) => a.name.localeCompare(b.name));
  for (const prim of ordered) {
    lines.push(`one sig ${prim.name} extends Prim {}`);
  }
  lines.push('');
}

function appendRegionFacts(lines, regions) {
  if (regions.length === 0) {
    return;
  }
  const ordered = [...regions].sort((a, b) => a.name.localeCompare(b.name));
  lines.push('fact RegionScopes {');
  for (const region of ordered) {
    lines.push(`  ${region.name}.scopes = ${formatSet(region.scopes)}`);
  }
  lines.push('}');
  lines.push('');

  lines.push('fact RegionChildren {');
  for (const region of ordered) {
    lines.push(`  ${region.name}.children = ${formatSet(region.children)}`);
  }
  lines.push('}');
  lines.push('');
}

function appendPrimFacts(lines, prims) {
  if (prims.length === 0) {
    return;
  }
  const ordered = [...prims].sort((a, b) => a.name.localeCompare(b.name));
  lines.push('fact PrimIds {');
  for (const prim of ordered) {
    lines.push(`  ${prim.name}.primId = ${stringLiteral(prim.primId)}`);
  }
  lines.push('}');
  lines.push('');

  lines.push('fact PrimScopeNeeds {');
  for (const prim of ordered) {
    lines.push(`  ${prim.name}.scopeNeed = ${formatSet(prim.scopeNeeds)}`);
  }
  lines.push('}');
  lines.push('');
}

function formatSet(values) {
  if (!values || values.size === 0) {
    return 'none';
  }
  const list = Array.from(values).sort();
  if (list.length === 1) {
    return list[0];
  }
  return list.join(' + ');
}

function stringLiteral(value) {
  if (typeof value !== 'string') {
    return '""';
  }
  return `"${value.replace(/"/g, '\\"')}"`;
}

function isNonEmptyString(value) {
  return typeof value === 'string' && value.trim().length > 0;
}
