const REGION_PREFIX = 'Region';
const PRIM_PREFIX = 'Prim';
const SCOPE_PREFIX = 'Scope';

export function emitAuthorizeAlloy(ir, options = {}) {
  const rules = normalizeRules(options.rules);
  const context = {
    scopeByValue: new Map(),
    scopeByName: new Map(),
    scopesInOrder: [],
    regions: [],
    prims: []
  };

  const root = createRegion(context, []);
  processNode(ir, root, context, rules);

  const lines = [];
  lines.push('open util/ordering[Node]');
  lines.push('');
  lines.push('sig Node {}');
  lines.push('sig Region extends Node { scopes: set Scope, children: set Node }');
  lines.push('sig Prim extends Node { primId: one String, scopeNeed: set Scope }');
  lines.push('sig Scope {}');
  lines.push('');
  lines.push('pred Dominates[r: Region, n: Node] { n in r.*children }');
  lines.push('pred Covered[n: Prim] { some r: Region | Dominates[r, n] and some (r.scopes & n.scopeNeed) }');
  lines.push('pred MissingAuth { some n: Prim | some n.scopeNeed and not Covered[n] }');
  lines.push('');

  appendScopeDecls(lines, context);
  appendRegionDecls(lines, context);
  appendPrimDecls(lines, context);

  appendScopeFacts(lines, context);
  appendRegionFacts(lines, context);
  appendPrimFacts(lines, context);

  lines.push('run { MissingAuth }');
  lines.push('run { not MissingAuth }');

  return lines.join('\n') + '\n';
}

function processNode(node, currentRegion, context, rules) {
  if (node == null) {
    return;
  }

  if (Array.isArray(node)) {
    for (const child of node) {
      processNode(child, currentRegion, context, rules);
    }
    return;
  }

  if (typeof node !== 'object') {
    return;
  }

  if (node.node === 'Region' && node.kind === 'Authorize') {
    const scopes = extractRegionScopes(node);
    const region = createRegion(context, scopes);
    registerChild(currentRegion, region.name);
    for (const child of node.children || []) {
      processNode(child, region, context, rules);
    }
    return;
  }

  if (node.node === 'Prim') {
    const prim = createPrim(node, context, rules);
    registerChild(currentRegion, prim.name);
    return;
  }

  for (const child of node.children || []) {
    processNode(child, currentRegion, context, rules);
  }
}

function createRegion(context, scopes) {
  const name = `${REGION_PREFIX}${context.regions.length}`;
  const scopeNames = mapScopes(scopes, context);
  const entry = { name, scopes: scopeNames, children: new Set() };
  context.regions.push(entry);
  return entry;
}

function createPrim(node, context, rules) {
  const name = `${PRIM_PREFIX}${context.prims.length}`;
  const info = resolvePrimInfo(node, rules);
  const scopeNames = mapScopes(info.scopes, context);
  const entry = {
    name,
    primId: info.primId,
    scopes: scopeNames
  };
  context.prims.push(entry);
  return entry;
}

function registerChild(region, childName) {
  if (!region || !childName) {
    return;
  }
  region.children.add(childName);
}

function appendScopeDecls(lines, context) {
  if (context.scopesInOrder.length === 0) {
    return;
  }
  for (const scope of context.scopesInOrder) {
    lines.push(`one sig ${scope.name} extends Scope {}`);
    lines.push(`// ${scope.name} => "${scope.value}"`);
  }
  lines.push('');
}

function appendRegionDecls(lines, context) {
  if (context.regions.length === 0) {
    return;
  }
  for (const region of context.regions) {
    lines.push(`one sig ${region.name} extends Region {}`);
  }
  lines.push('');
}

function appendPrimDecls(lines, context) {
  if (context.prims.length === 0) {
    return;
  }
  for (const prim of context.prims) {
    lines.push(`one sig ${prim.name} extends Prim {}`);
  }
  lines.push('');
}

function appendScopeFacts(lines, context) {
  if (context.scopesInOrder.length === 0) {
    return;
  }
  lines.push('fact ScopeUniverse {');
  const names = context.scopesInOrder.map((scope) => scope.name);
  lines.push(`  Scope = ${names.join(' + ')}`);
  lines.push('}');
  lines.push('');
}

function appendRegionFacts(lines, context) {
  if (context.regions.length === 0) {
    return;
  }
  lines.push('fact RegionScopes {');
  for (const region of context.regions) {
    lines.push(`  ${region.name}.scopes = ${formatSet(region.scopes)}`);
  }
  lines.push('}');
  lines.push('');

  lines.push('fact RegionChildren {');
  for (const region of context.regions) {
    lines.push(`  ${region.name}.children = ${formatSet([...region.children].sort())}`);
  }
  lines.push('}');
  lines.push('');
}

function appendPrimFacts(lines, context) {
  if (context.prims.length === 0) {
    return;
  }
  lines.push('fact PrimIds {');
  for (const prim of context.prims) {
    lines.push(`  ${prim.name}.primId = "${escapeString(prim.primId)}"`);
  }
  lines.push('}');
  lines.push('');

  lines.push('fact PrimScopeNeeds {');
  for (const prim of context.prims) {
    lines.push(`  ${prim.name}.scopeNeed = ${formatSet(prim.scopes)}`);
  }
  lines.push('}');
  lines.push('');
}

function formatSet(values) {
  if (!values || values.length === 0) {
    return 'none';
  }
  if (values.length === 1) {
    return values[0];
  }
  const sorted = [...values].sort();
  return sorted.join(' + ');
}

function mapScopes(scopes, context) {
  if (!Array.isArray(scopes)) {
    return [];
  }
  const seen = new Set();
  for (const scope of scopes) {
    const key = normalizeScopeValue(scope);
    if (!key) {
      continue;
    }
    const entry = internScope(key, context);
    if (entry) {
      seen.add(entry.name);
    }
  }
  const names = [...seen];
  names.sort((a, b) => getScopeIndex(a, context) - getScopeIndex(b, context));
  return names;
}

function internScope(value, context) {
  const existing = context.scopeByValue.get(value);
  if (existing) {
    return existing;
  }
  const entry = {
    value,
    name: `${SCOPE_PREFIX}${context.scopesInOrder.length}`,
    index: context.scopesInOrder.length
  };
  context.scopeByValue.set(value, entry);
  context.scopeByName.set(entry.name, entry);
  context.scopesInOrder.push(entry);
  return entry;
}

function getScopeIndex(name, context) {
  const entry = context.scopeByName.get(name);
  return entry ? entry.index : Number.MAX_SAFE_INTEGER;
}

function normalizeScopeValue(value) {
  if (typeof value === 'string') {
    const trimmed = value.trim();
    if (trimmed.length === 0) {
      return null;
    }
    return trimmed;
  }
  return null;
}

function extractRegionScopes(node) {
  const raw = node?.attrs?.scope;
  if (Array.isArray(raw)) {
    return raw
      .map((entry) => normalizeScopeValue(entry))
      .filter((entry) => entry !== null);
  }
  if (typeof raw === 'string') {
    return raw
      .split(',')
      .map((part) => normalizeScopeValue(part))
      .filter((part) => part !== null);
  }
  return [];
}

function resolvePrimInfo(node, rules) {
  const canonicalId = extractCanonicalId(node);
  const byId = canonicalId ? rules.byId.get(canonicalId) : null;
  if (byId) {
    return { primId: canonicalId, scopes: [...byId] };
  }

  const name = typeof node?.prim === 'string' ? node.prim.toLowerCase() : '';
  if (name) {
    const fallback = rules.byBase.get(name);
    if (fallback) {
      return { primId: fallback.id, scopes: [...fallback.scopes] };
    }
  }

  return { primId: canonicalId || name || 'unknown', scopes: [] };
}

function extractCanonicalId(node) {
  const candidates = [
    node?.impl?.id,
    node?.impl?.canonical_id,
    node?.impl?.canonical?.id,
    node?.prim_id,
    node?.primId,
    node?.id
  ];
  for (const candidate of candidates) {
    if (typeof candidate === 'string' && candidate.length > 0) {
      return candidate;
    }
  }
  return null;
}

function normalizeRules(rules) {
  const byId = new Map();
  const byBase = new Map();
  const source = rules && typeof rules === 'object' ? rules : {};

  for (const [key, value] of Object.entries(source)) {
    if (typeof key !== 'string' || key.length === 0) {
      continue;
    }
    if (!Array.isArray(value)) {
      continue;
    }
    const scopes = value
      .map((entry) => normalizeScopeValue(entry))
      .filter((entry) => entry !== null);
    if (scopes.length === 0) {
      continue;
    }
    const uniqueScopes = [...new Set(scopes)].sort();
    byId.set(key, uniqueScopes);
    const base = extractBaseName(key);
    if (base) {
      const existing = byBase.get(base);
      if (!existing || key.localeCompare(existing.id) < 0) {
        byBase.set(base, { id: key, scopes: uniqueScopes });
      }
    }
  }

  return { byId, byBase };
}

function extractBaseName(id) {
  if (typeof id !== 'string') {
    return '';
  }
  const slash = id.lastIndexOf('/');
  const start = slash >= 0 ? slash + 1 : 0;
  const segment = id.slice(start);
  const at = segment.indexOf('@');
  const base = at >= 0 ? segment.slice(0, at) : segment;
  return base.toLowerCase();
}

function escapeString(value) {
  if (typeof value !== 'string') {
    return '';
  }
  return value.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
}
