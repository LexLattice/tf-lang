const REGION_PREFIX = 'Region';
const PRIM_PREFIX = 'Prim';

export function emitAlloyAuthorize(ir, options = {}) {
  const rules = normalizeRules(options.rules);
  const context = {
    regions: [],
    prims: [],
    scopeStrings: new Set(),
    regionCounter: 0,
    primCounter: 0,
    rules,
  };

  processNode(ir, context);

  const scopeNames = assignScopeNames(context.scopeStrings);
  for (const region of context.regions) {
    region.scopes = region.scopeStrings.map((scope) => scopeNames.get(scope));
    delete region.scopeStrings;
    region.children.sort();
  }
  for (const prim of context.prims) {
    prim.scopeNeed = prim.scopeNeedStrings.map((scope) => scopeNames.get(scope));
    delete prim.scopeNeedStrings;
  }

  const scopes = [...scopeNames.entries()]
    .map(([scope, name]) => ({ scope, name }))
    .sort((a, b) => a.name.localeCompare(b.name));

  const lines = [];
  lines.push('open util/ordering[Node]');
  lines.push('');
  lines.push('sig Node {}');
  lines.push('sig Region extends Node { scopes: set Scope, children: set Node }');
  lines.push('sig Prim extends Node { primId: one String, scopeNeed: set Scope }');
  lines.push('sig Scope {}');
  lines.push('');

  if (scopes.length > 0) {
    for (const scope of scopes) {
      lines.push(`one sig ${scope.name} extends Scope {}`);
    }
    lines.push('');
  }

  if (context.regions.length > 0) {
    for (const region of context.regions) {
      lines.push(`one sig ${region.name} extends Region {}`);
    }
    lines.push('');
  }

  if (context.prims.length > 0) {
    for (const prim of context.prims) {
      lines.push(`one sig ${prim.name} extends Prim {}`);
    }
    lines.push('');
  }

  if (context.regions.length > 0) {
    lines.push('fact RegionScopes {');
    for (const region of context.regions) {
      lines.push(`  ${region.name}.scopes = ${formatSet(region.scopes)}`);
    }
    lines.push('}');
    lines.push('');

    lines.push('fact RegionChildren {');
    for (const region of context.regions) {
      lines.push(`  ${region.name}.children = ${formatSet(region.children)}`);
    }
    lines.push('}');
    lines.push('');
  }

  if (context.prims.length > 0) {
    lines.push('fact PrimAttrs {');
    for (const prim of context.prims) {
      lines.push(`  ${prim.name}.primId = ${stringLiteral(prim.primId)}`);
      lines.push(`  ${prim.name}.scopeNeed = ${formatSet(prim.scopeNeed)}`);
    }
    lines.push('}');
    lines.push('');
  }

  lines.push('pred Dominates[r:Region, n:Node] { n in r.*children }');
  lines.push('pred Covered[n:Prim] { some r:Region | Dominates[r, n] and some (r.scopes & n.scopeNeed) }');
  lines.push('pred MissingAuth { some n:Prim | some n.scopeNeed and not Covered[n] }');
  lines.push('');
  lines.push('run { MissingAuth }');
  lines.push('run { not MissingAuth }');
  lines.push('');

  return lines.join('\n') + '\n';
}

function processNode(node, context) {
  if (!node || typeof node !== 'object') {
    return null;
  }

  if (Array.isArray(node)) {
    for (const child of node) {
      processNode(child, context);
    }
    return null;
  }

  if (node.node === 'Prim') {
    return registerPrim(node, context);
  }

  return registerRegion(node, context);
}

function registerRegion(node, context) {
  const name = `${REGION_PREFIX}${context.regionCounter}`;
  context.regionCounter += 1;

  const scopes = extractAuthorizeScopes(node);
  for (const scope of scopes) {
    context.scopeStrings.add(scope);
  }

  const entry = {
    type: 'Region',
    name,
    scopeStrings: scopes,
    children: [],
  };

  context.regions.push(entry);

  const children = Array.isArray(node.children) ? node.children : [];
  for (const child of children) {
    const childName = processNode(child, context);
    if (childName) {
      entry.children.push(childName);
    }
  }

  return entry.name;
}

function registerPrim(node, context) {
  const name = `${PRIM_PREFIX}${context.primCounter}`;
  context.primCounter += 1;

  const primId = resolvePrimId(node);
  const scopeNeedStrings = resolvePrimScopes(node, primId, context.rules);
  for (const scope of scopeNeedStrings) {
    context.scopeStrings.add(scope);
  }

  const entry = {
    type: 'Prim',
    name,
    primId,
    scopeNeedStrings,
  };

  context.prims.push(entry);

  return entry.name;
}

function extractAuthorizeScopes(node) {
  if (!node || node.node !== 'Region' || node.kind !== 'Authorize') {
    return [];
  }
  const raw = typeof node?.attrs?.scope === 'string' ? node.attrs.scope : '';
  return normalizeScopeList(raw);
}

function normalizeScopeList(raw) {
  if (!raw || typeof raw !== 'string') {
    return [];
  }
  const scopes = raw
    .split(',')
    .map((scope) => scope.trim())
    .filter((scope) => scope.length > 0);
  scopes.sort((a, b) => a.localeCompare(b));
  return scopes;
}

function resolvePrimId(node) {
  const candidates = [
    node?.impl?.canonical?.id,
    node?.impl?.canonical_id,
    node?.impl?.id,
    node?.prim_id,
    node?.primId,
    node?.id,
  ];

  for (const candidate of candidates) {
    if (typeof candidate === 'string' && candidate.length > 0) {
      return candidate;
    }
  }

  if (typeof node?.prim === 'string' && node.prim.length > 0) {
    return node.prim;
  }

  return nameFallback('prim');
}

function resolvePrimScopes(node, primId, rules) {
  if (typeof primId === 'string' && rules.byId.has(primId)) {
    return rules.byId.get(primId).scopes;
  }

  const primName = typeof node?.prim === 'string' ? node.prim.toLowerCase() : '';
  if (!primName) {
    return [];
  }

  const matches = rules.byName.get(primName);
  if (!matches || matches.length === 0) {
    return [];
  }

  return matches[0].scopes;
}

function normalizeRules(rawRules = {}) {
  const byId = new Map();
  const byName = new Map();

  for (const [id, scopes] of Object.entries(rawRules)) {
    if (typeof id !== 'string' || id.length === 0) {
      continue;
    }
    const normalizedScopes = normalizeScopes(scopes);
    const entry = { id, scopes: normalizedScopes };
    byId.set(id, entry);

    const base = extractBaseName(id);
    if (!base) {
      continue;
    }
    if (!byName.has(base)) {
      byName.set(base, []);
    }
    byName.get(base).push(entry);
  }

  for (const entries of byName.values()) {
    entries.sort((a, b) => a.id.localeCompare(b.id));
  }

  return { byId, byName };
}

function normalizeScopes(scopes) {
  if (!Array.isArray(scopes)) {
    return [];
  }
  const filtered = scopes
    .filter((scope) => typeof scope === 'string' && scope.length > 0)
    .map((scope) => scope.trim())
    .filter((scope) => scope.length > 0);
  filtered.sort((a, b) => a.localeCompare(b));
  return filtered;
}

function extractBaseName(id) {
  if (typeof id !== 'string') {
    return '';
  }
  const slashIndex = id.lastIndexOf('/');
  const atIndex = id.indexOf('@', slashIndex >= 0 ? slashIndex : 0);
  const start = slashIndex >= 0 ? slashIndex + 1 : 0;
  const end = atIndex >= 0 ? atIndex : id.length;
  return id.slice(start, end).toLowerCase();
}

function assignScopeNames(scopeStrings) {
  const sorted = [...scopeStrings].sort((a, b) => a.localeCompare(b));
  const names = new Map();
  const used = new Set();
  for (const scope of sorted) {
    const base = `Scope_${sanitizeSymbol(scope)}`;
    let name = base;
    let index = 1;
    while (used.has(name)) {
      index += 1;
      name = `${base}_${index}`;
    }
    names.set(scope, name);
    used.add(name);
  }
  return names;
}

function sanitizeSymbol(text) {
  const replaced = text.replace(/[^A-Za-z0-9]/g, '_');
  if (replaced.length === 0) {
    return 'Scope';
  }
  return replaced;
}

function formatSet(items) {
  if (!items || items.length === 0) {
    return 'none';
  }
  if (items.length === 1) {
    return items[0];
  }
  const sorted = [...items].sort();
  return sorted.join(' + ');
}

function stringLiteral(text) {
  const escaped = String(text ?? '')
    .replace(/\\/g, '\\\\')
    .replace(/"/g, '\\"');
  return `"${escaped}"`;
}

function nameFallback(prefix) {
  return `${prefix}_unknown`;
}

