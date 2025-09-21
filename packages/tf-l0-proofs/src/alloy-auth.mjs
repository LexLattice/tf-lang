const REGION_PREFIX = 'Region';
const PRIM_PREFIX = 'Prim';
const SCOPE_PREFIX = 'Scope';

export function emitAuthorizeAlloy(ir, options = {}) {
  const rules = normalizeRules(options.rules);
  const scopeHint = normalizeScopeOption(options.scope);
  const context = {
    scopeByValue: new Map(),
    scopeByName: new Map(),
    scopesInOrder: [],
    regions: [],
    prims: []
  };

  const root = createRegion(context, []);
  processNode(ir, root, context, rules);

  const lines = ['open util/ordering[Node]'];

  pushSection(lines, buildSignatureSection(context));
  pushSection(lines, buildPredicateAndFactSection(context));
  pushSection(lines, buildRunSection(scopeHint));

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

function buildSignatureSection(context) {
  const lines = [
    'sig Node {}',
    'sig Region extends Node { scopes: set Scope, children: set Node }',
    'sig Prim extends Node { primId: one String, scopeNeed: set Scope }',
    'sig Scope {}'
  ];

  const scopeDecls = buildScopeDeclarations(context);
  if (scopeDecls.length > 0) {
    lines.push('');
    lines.push(...scopeDecls);
  }

  const regionDecls = buildRegionDeclarations(context);
  if (regionDecls.length > 0) {
    lines.push('');
    lines.push(...regionDecls);
  }

  const primDecls = buildPrimDeclarations(context);
  if (primDecls.length > 0) {
    lines.push('');
    lines.push(...primDecls);
  }

  return lines;
}

function buildPredicateAndFactSection(context) {
  const lines = [
    'pred Dominates[r: Region, n: Node] { n in r.*children }',
    'pred Covered[n: Prim] { some r: Region | Dominates[r, n] and some (r.scopes & n.scopeNeed) }',
    'pred MissingAuth { some n: Prim | some n.scopeNeed and not Covered[n] }'
  ];

  const factLines = buildFactLines(context);
  if (factLines.length > 0) {
    lines.push('');
    lines.push(...factLines);
  }

  return lines;
}

function buildRunSection(scopeHint) {
  return [
    formatRunCommand('MissingAuth', scopeHint),
    formatRunCommand('not MissingAuth', scopeHint)
  ];
}

function buildScopeDeclarations(context) {
  const scopes = [...context.scopesInOrder].sort((a, b) =>
    a.name.localeCompare(b.name)
  );
  const lines = [];
  for (const scope of scopes) {
    lines.push(`one sig ${scope.name} extends Scope {}`);
    lines.push(`// ${scope.name} => "${scope.value}"`);
  }
  return lines;
}

function buildRegionDeclarations(context) {
  const regions = [...context.regions].sort((a, b) =>
    a.name.localeCompare(b.name)
  );
  return regions.map((region) => `one sig ${region.name} extends Region {}`);
}

function buildPrimDeclarations(context) {
  const prims = [...context.prims].sort((a, b) => a.name.localeCompare(b.name));
  return prims.map((prim) => `one sig ${prim.name} extends Prim {}`);
}

function buildFactLines(context) {
  const lines = [];
  const scopes = [...context.scopesInOrder].sort((a, b) =>
    a.name.localeCompare(b.name)
  );
  if (scopes.length > 0) {
    lines.push('fact ScopeUniverse {');
    const names = scopes.map((scope) => scope.name);
    lines.push(`  Scope = ${names.join(' + ')}`);
    lines.push('}');
  }

  const regions = [...context.regions].sort((a, b) =>
    a.name.localeCompare(b.name)
  );
  if (regions.length > 0) {
    if (lines.length > 0) {
      lines.push('');
    }
    lines.push('fact RegionScopes {');
    for (const region of regions) {
      lines.push(`  ${region.name}.scopes = ${formatSet(region.scopes)}`);
    }
    lines.push('}');
    lines.push('');
    lines.push('fact RegionChildren {');
    for (const region of regions) {
      const children = [...region.children].sort();
      lines.push(`  ${region.name}.children = ${formatSet(children)}`);
    }
    lines.push('}');
  }

  const prims = [...context.prims].sort((a, b) => a.name.localeCompare(b.name));
  if (prims.length > 0) {
    if (lines.length > 0) {
      lines.push('');
    }
    lines.push('fact PrimIds {');
    for (const prim of prims) {
      lines.push(`  ${prim.name}.primId = "${escapeString(prim.primId)}"`);
    }
    lines.push('}');
    lines.push('');
    lines.push('fact PrimScopeNeeds {');
    for (const prim of prims) {
      lines.push(`  ${prim.name}.scopeNeed = ${formatSet(prim.scopes)}`);
    }
    lines.push('}');
  }

  return lines;
}

function formatRunCommand(body, scopeHint) {
  if (scopeHint == null) {
    return `run { ${body} }`;
  }
  return `run { ${body} } for ${scopeHint}`;
}

function normalizeScopeOption(value) {
  if (value == null) {
    return null;
  }
  const numeric = typeof value === 'number' ? value : Number.parseInt(value, 10);
  if (!Number.isFinite(numeric) || !Number.isInteger(numeric) || numeric <= 0) {
    throw new Error('scope option must be a positive integer');
  }
  return numeric;
}

function pushSection(target, section) {
  const lines = trimSection(section);
  if (lines.length === 0) {
    return;
  }
  if (target.length > 0) {
    target.push('');
  }
  target.push(...lines);
}

function trimSection(section) {
  const lines = [...section];
  while (lines.length > 0 && lines[0] === '') {
    lines.shift();
  }
  while (lines.length > 0 && lines[lines.length - 1] === '') {
    lines.pop();
  }
  return lines;
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
