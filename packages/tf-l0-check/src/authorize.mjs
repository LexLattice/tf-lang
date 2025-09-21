const PROTECTED_NAMES = ['sign-data', 'encrypt', 'decrypt'];

const DEFAULT_OPTS = {
  warnUnused: false,
  strictWarnsFail: false
};

export function checkAuthorize(ir, catalog, rules, opts = DEFAULT_OPTS) {
  const options = { ...DEFAULT_OPTS, ...(opts || {}) };
  const ruleMap = buildRuleMap(rules);
  const reasons = [];
  const warnings = [];

  function visit(node, stack) {
    if (node == null) {
      return;
    }
    if (Array.isArray(node)) {
      for (const child of node) {
        visit(child, stack);
      }
      return;
    }
    if (typeof node !== 'object') {
      return;
    }

    if (node.node === 'Region') {
      if (node.kind === 'Authorize') {
        const scopes = extractScopes(node.attrs);
        const entry = { scopes, used: false };
        const nextStack = stack.concat(entry);
        const children = Array.isArray(node.children) ? node.children : [];
        for (const child of children) {
          visit(child, nextStack);
        }
        if (options.warnUnused && !entry.used) {
          for (const scope of entry.scopes) {
            warnings.push(`auth: unused authorize scope "${scope}"`);
          }
        }
        return;
      }
      const children = Array.isArray(node.children) ? node.children : [];
      for (const child of children) {
        visit(child, stack);
      }
      return;
    }

    if (node.node === 'Prim') {
      handlePrim(node, stack);
      return;
    }

    const children = Array.isArray(node.children) ? node.children : [];
    for (const child of children) {
      visit(child, stack);
    }
  }

  function handlePrim(node, stack) {
    const baseName = normalizeName(node.prim);
    if (!baseName) {
      return;
    }

    const catalogEntry = lookupCatalogEntry(catalog, node, baseName);
    const canonicalCandidates = [];
    const fromNode = inferCanonicalId(node);
    if (fromNode) {
      canonicalCandidates.push(fromNode);
    }
    if (catalogEntry?.id && !canonicalCandidates.includes(catalogEntry.id)) {
      canonicalCandidates.push(catalogEntry.id);
    }

    let matchedId = null;
    let requiredScopes = [];
    for (const candidate of canonicalCandidates) {
      const scopes = getRuleScopes(ruleMap, candidate);
      if (scopes.length > 0) {
        matchedId = candidate;
        requiredScopes = scopes;
        break;
      }
    }

    if (requiredScopes.length === 0 && catalogEntry && isCryptoPrimitive(catalogEntry, baseName)) {
      const scopes = getRuleScopes(ruleMap, catalogEntry.id);
      if (scopes.length > 0) {
        matchedId = catalogEntry.id;
        requiredScopes = scopes;
      }
    }

    if (requiredScopes.length === 0) {
      return;
    }

    const label = matchedId || baseName;

    if (stack.length === 0) {
      reasons.push(`auth: ${label} requires Authorize{scope in [${requiredScopes.join(', ')}]}`);
      return;
    }

    const matchedAuthorize = findMatchingAuthorize(stack, requiredScopes);
    if (matchedAuthorize) {
      matchedAuthorize.used = true;
      return;
    }

    const haveScopes = collectScopes(stack);
    reasons.push(`auth: scope mismatch for ${label} (have [${haveScopes.join(', ')}], need one of [${requiredScopes.join(', ')}])`);
  }

  visit(ir, []);

  const ok = reasons.length === 0 && (!options.strictWarnsFail || warnings.length === 0);
  return { ok, reasons, warnings };
}

function buildRuleMap(rules) {
  const map = new Map();
  if (!rules || typeof rules !== 'object') {
    return map;
  }
  const entries = rules instanceof Map ? rules.entries() : Object.entries(rules);
  for (const [key, value] of entries) {
    if (typeof key !== 'string') {
      continue;
    }
    const normalizedKey = key.toLowerCase();
    if (Array.isArray(value)) {
      const scopes = value.filter((v) => typeof v === 'string' && v.length > 0);
      map.set(normalizedKey, scopes);
      continue;
    }
    if (typeof value === 'string' && value.length > 0) {
      map.set(normalizedKey, [value]);
    }
  }
  return map;
}

function getRuleScopes(ruleMap, canonicalId) {
  if (!canonicalId || typeof canonicalId !== 'string') {
    return [];
  }
  const scopes = ruleMap.get(canonicalId.toLowerCase());
  if (!Array.isArray(scopes)) {
    return [];
  }
  return scopes;
}

function inferCanonicalId(node) {
  if (!node || typeof node !== 'object') {
    return null;
  }
  const candidates = [
    node.id,
    node.canonical,
    node.canonicalId,
    node.canonical_id,
    node?.spec?.id,
    node?.ref?.canonical,
    node?.ref?.canonicalId,
    node?.ref?.canonical_id
  ];
  for (const candidate of candidates) {
    if (typeof candidate === 'string' && candidate.includes('@')) {
      return candidate;
    }
  }
  return null;
}

function lookupCatalogEntry(catalog, node, baseName) {
  const primitives = Array.isArray(catalog?.primitives) ? catalog.primitives : [];
  if (primitives.length === 0) {
    return null;
  }
  const fromNode = inferCanonicalId(node);
  if (fromNode) {
    const lowerId = fromNode.toLowerCase();
    for (const prim of primitives) {
      if (typeof prim?.id === 'string' && prim.id.toLowerCase() === lowerId) {
        return prim;
      }
    }
  }
  if (!baseName) {
    return null;
  }
  const lowerName = baseName.toLowerCase();
  for (const prim of primitives) {
    if (typeof prim?.name === 'string' && prim.name.toLowerCase() === lowerName) {
      return prim;
    }
  }
  const idRegex = new RegExp(`/${escapeRegex(lowerName)}@\\d+$`, 'i');
  for (const prim of primitives) {
    if (typeof prim?.id === 'string' && idRegex.test(prim.id)) {
      return prim;
    }
  }
  return null;
}

function extractScopes(attrs) {
  if (!attrs || typeof attrs !== 'object') {
    return [];
  }
  const values = [];
  if ('scope' in attrs) {
    values.push(attrs.scope);
  }
  if ('scopes' in attrs) {
    values.push(attrs.scopes);
  }
  const scopes = [];
  for (const value of values) {
    if (Array.isArray(value)) {
      for (const item of value) {
        if (typeof item === 'string' && item.length > 0) {
          scopes.push(item);
        }
      }
      continue;
    }
    if (typeof value === 'string' && value.length > 0) {
      scopes.push(value);
    }
  }
  return dedupe(scopes);
}

function dedupe(list) {
  const out = [];
  const seen = new Set();
  for (const item of list) {
    if (seen.has(item)) {
      continue;
    }
    seen.add(item);
    out.push(item);
  }
  return out;
}

function normalizeName(value) {
  if (typeof value !== 'string') {
    return '';
  }
  return value.toLowerCase();
}

function escapeRegex(value) {
  return value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function isCryptoPrimitive(entry, baseName) {
  if (!entry || typeof entry !== 'object') {
    return false;
  }
  const effects = Array.isArray(entry.effects) ? entry.effects : [];
  if (!effects.includes('Crypto')) {
    return false;
  }
  return PROTECTED_NAMES.includes(baseName.toLowerCase());
}

function findMatchingAuthorize(stack, requiredScopes) {
  for (let i = stack.length - 1; i >= 0; i -= 1) {
    const entry = stack[i];
    if (!entry || !Array.isArray(entry.scopes)) {
      continue;
    }
    for (const scope of entry.scopes) {
      if (requiredScopes.includes(scope)) {
        return entry;
      }
    }
  }
  return null;
}

function collectScopes(stack) {
  const set = new Set();
  for (const entry of stack) {
    if (!entry || !Array.isArray(entry.scopes)) {
      continue;
    }
    for (const scope of entry.scopes) {
      set.add(scope);
    }
  }
  return Array.from(set);
}
