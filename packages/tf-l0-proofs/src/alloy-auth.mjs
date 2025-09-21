import authorizeRules from '../../tf-l0-check/rules/authorize-scopes.json' with { type: 'json' };

export function emitAuthorizeAlloy(ir, options = {}) {
  const ruleIndex = buildRuleIndex(options.rules ?? authorizeRules);
  const context = createContext(ruleIndex);
  visit(ir, context, []);

  return serializeModel(context);
}

function createContext(ruleIndex) {
  return {
    ruleIndex,
    regions: [],
    regionMap: new Map(),
    prims: [],
    scopeNames: new Set()
  };
}

function visit(node, context, regionStack) {
  if (node == null) {
    return;
  }
  if (Array.isArray(node)) {
    for (const child of node) {
      visit(child, context, regionStack);
    }
    return;
  }
  if (typeof node !== 'object') {
    return;
  }

  if (node.node === 'Region' && node.kind === 'Authorize') {
    handleAuthorizeRegion(node, context, regionStack);
    return;
  }

  if (node.node === 'Prim') {
    handlePrimNode(node, context, regionStack);
    return;
  }

  const children = Array.isArray(node.children) ? node.children : [];
  for (const child of children) {
    visit(child, context, regionStack);
  }
}

function handleAuthorizeRegion(node, context, regionStack) {
  const scopes = extractRegionScopes(node);
  const region = registerRegion(scopes, context);

  for (const ancestorName of regionStack) {
    addChild(context, ancestorName, region.name);
  }

  regionStack.push(region.name);
  const children = Array.isArray(node.children) ? node.children : [];
  for (const child of children) {
    visit(child, context, regionStack);
  }
  regionStack.pop();
}

function handlePrimNode(node, context, regionStack) {
  const analysis = analyzePrim(node, context.ruleIndex);
  if (!analysis || analysis.scopes.length === 0) {
    return;
  }

  const name = `Prim${context.prims.length}`;
  const prim = {
    name,
    display: analysis.display,
    scopeNeed: analysis.scopes
  };
  context.prims.push(prim);

  for (const scope of analysis.scopes) {
    context.scopeNames.add(scope);
  }

  for (const regionName of regionStack) {
    addChild(context, regionName, prim.name);
  }
}

function registerRegion(scopes, context) {
  const name = `Region${context.regions.length}`;
  const entry = {
    name,
    scopes,
    children: new Set()
  };
  context.regions.push(entry);
  context.regionMap.set(name, entry);
  for (const scope of scopes) {
    context.scopeNames.add(scope);
  }
  return entry;
}

function addChild(context, regionName, childName) {
  const region = context.regionMap.get(regionName);
  if (!region) {
    return;
  }
  region.children.add(childName);
}

function extractRegionScopes(node) {
  const raw = node?.attrs?.scope;
  if (typeof raw !== 'string') {
    return [];
  }
  const scopes = raw
    .split(',')
    .map((scope) => scope.trim())
    .filter((scope) => scope.length > 0);
  const unique = [...new Set(scopes.map((scope) => scope.toLowerCase()))];
  unique.sort((a, b) => a.localeCompare(b));
  return unique;
}

function analyzePrim(node, ruleIndex) {
  const canonicalId = extractCanonicalId(node);
  const byIdScopes = canonicalId ? ruleIndex.byId.get(canonicalId) ?? [] : [];
  if (byIdScopes.length > 0) {
    return { display: canonicalId, scopes: byIdScopes };
  }

  const baseName = extractBaseName(node, canonicalId);
  if (!baseName) {
    return null;
  }
  const fallback = ruleIndex.byBase.get(baseName);
  if (!fallback || fallback.scopes.length === 0) {
    return null;
  }
  const display = canonicalId ?? fallback.id ?? baseName;
  return { display, scopes: fallback.scopes };
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

function extractBaseName(node, canonicalId) {
  if (typeof canonicalId === 'string') {
    const base = baseNameFromId(canonicalId);
    if (base) {
      return base;
    }
  }
  const name = typeof node?.prim === 'string' ? node.prim : null;
  if (name && name.length > 0) {
    return name.toLowerCase();
  }
  return null;
}

function baseNameFromId(id) {
  if (typeof id !== 'string') {
    return null;
  }
  const match = id.match(/\/([^/@]+)@/);
  if (match) {
    return match[1].toLowerCase();
  }
  const trimmed = id.trim();
  if (!trimmed) {
    return null;
  }
  const slashIndex = trimmed.lastIndexOf('/');
  const segment = slashIndex >= 0 ? trimmed.slice(slashIndex + 1) : trimmed;
  const atIndex = segment.indexOf('@');
  const base = atIndex >= 0 ? segment.slice(0, atIndex) : segment;
  return base.toLowerCase();
}

function buildRuleIndex(rules) {
  const byId = new Map();
  const byBase = new Map();
  const entries = rules && typeof rules === 'object' ? Object.entries(rules) : [];
  for (const [id, scopes] of entries) {
    if (typeof id !== 'string') {
      continue;
    }
    const normalizedScopes = normalizeScopes(scopes);
    byId.set(id, normalizedScopes);
    const base = baseNameFromId(id);
    if (base && !byBase.has(base)) {
      byBase.set(base, { id, scopes: normalizedScopes });
    }
  }
  return { byId, byBase };
}

function normalizeScopes(scopes) {
  if (!Array.isArray(scopes)) {
    return [];
  }
  const unique = new Set();
  for (const scope of scopes) {
    if (typeof scope !== 'string') {
      continue;
    }
    const trimmed = scope.trim();
    if (trimmed.length > 0) {
      unique.add(trimmed.toLowerCase());
    }
  }
  return Array.from(unique).sort((a, b) => a.localeCompare(b));
}

function serializeModel(context) {
  const regions = [...context.regions].sort((a, b) => a.name.localeCompare(b.name));
  const prims = [...context.prims].sort((a, b) => a.name.localeCompare(b.name));
  const scopeValues = Array.from(context.scopeNames).sort((a, b) => a.localeCompare(b));
  const scopeAtoms = new Map();
  scopeValues.forEach((scope, index) => {
    scopeAtoms.set(scope, `Scope${index}`);
  });

  const lines = [];
  lines.push('module tf_lang_auth');
  lines.push('open util/ordering[Node]');
  lines.push('open util/strings');
  lines.push('');
  lines.push('sig Node {}');
  lines.push('sig Region extends Node { scopes: set Scope, children: set Node }');
  lines.push('sig Prim extends Node { primId: one String, scopeNeed: set Scope }');
  lines.push('sig Scope {}');
  lines.push('');

  if (scopeValues.length > 0) {
    for (const scope of scopeValues) {
      lines.push(`one sig ${scopeAtoms.get(scope)} extends Scope {}`);
    }
    lines.push('');
  }

  if (regions.length > 0) {
    for (const region of regions) {
      lines.push(`one sig ${region.name} extends Region {}`);
    }
    lines.push('');
  }

  if (prims.length > 0) {
    for (const prim of prims) {
      lines.push(`one sig ${prim.name} extends Prim {}`);
    }
    lines.push('');
  }

  if (regions.length > 0) {
    lines.push('fact RegionScopes {');
    for (const region of regions) {
      lines.push(`  ${region.name}.scopes = ${formatSet(region.scopes.map((scope) => scopeAtoms.get(scope)))}`);
    }
    lines.push('}');
    lines.push('');
  }

  if (regions.length > 0) {
    lines.push('fact RegionChildren {');
    for (const region of regions) {
      const children = Array.from(region.children).sort((a, b) => a.localeCompare(b));
      lines.push(`  ${region.name}.children = ${formatSet(children)}`);
    }
    lines.push('}');
    lines.push('');
  }

  if (prims.length > 0) {
    lines.push('fact PrimIds {');
    for (const prim of prims) {
      lines.push(`  ${prim.name}.primId = ${stringLiteral(prim.display)}`);
    }
    lines.push('}');
    lines.push('');

    lines.push('fact PrimScopes {');
    for (const prim of prims) {
      const scopes = prim.scopeNeed.map((scope) => scopeAtoms.get(scope));
      lines.push(`  ${prim.name}.scopeNeed = ${formatSet(scopes)}`);
    }
    lines.push('}');
    lines.push('');
  }

  lines.push('pred Dominates[r: Region, n: Node] { n in r.*children }');
  lines.push('pred Covered[n: Prim] { some r: Region | Dominates[r, n] and some (r.scopes & n.scopeNeed) }');
  lines.push('pred MissingAuth { some n: Prim | some n.scopeNeed and not Covered[n] }');
  lines.push('');
  lines.push('run { MissingAuth }');
  lines.push('run { not MissingAuth }');
  lines.push('');
  return lines.join('\n');
}

function formatSet(values) {
  const filtered = values.filter((value) => typeof value === 'string' && value.length > 0);
  if (filtered.length === 0) {
    return 'none';
  }
  const sorted = [...new Set(filtered)].sort((a, b) => a.localeCompare(b));
  if (sorted.length === 1) {
    return sorted[0];
  }
  return sorted.join(' + ');
}

function stringLiteral(value) {
  if (typeof value !== 'string') {
    return '""';
  }
  return `"${value.replace(/\\/g, '\\\\').replace(/"/g, '\\"')}"`;
}
