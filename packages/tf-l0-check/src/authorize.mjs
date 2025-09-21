const DEFAULT_OPTS = {
  warnUnused: false,
  strictWarnsFail: false
};

const PROTECTED_NAME_PATTERN = /^(sign-data|encrypt|decrypt)$/i;

export function checkAuthorize(ir, catalog, rules, opts = {}) {
  const options = { ...DEFAULT_OPTS, ...(opts || {}) };
  const normalizedRules = isObject(rules) ? rules : {};
  const reasons = [];
  const warnings = [];
  const scopeStack = [];
  const authorizeEntries = [];

  visit(ir);

  if (options.warnUnused) {
    for (const entry of authorizeEntries) {
      for (const scope of entry.scopes) {
        if (!entry.usedScopes.has(scope)) {
          warnings.push(`auth: unused authorize scope "${scope}"`);
        }
      }
    }
  }

  const ok =
    reasons.length === 0 && (!options.strictWarnsFail || warnings.length === 0);

  return { ok, reasons, warnings };

  function visit(node) {
    if (node == null) {
      return;
    }

    if (Array.isArray(node)) {
      for (const child of node) {
        visit(child);
      }
      return;
    }

    if (typeof node !== 'object') {
      return;
    }

    if (node.node === 'Region' && node.kind === 'Authorize') {
      const scopes = extractAuthorizeScopes(node?.attrs);
      const entry = { scopes, usedScopes: new Set() };
      scopeStack.push(entry);
      authorizeEntries.push(entry);
      for (const child of node.children || []) {
        visit(child);
      }
      scopeStack.pop();
      return;
    }

    if (node.node === 'Prim') {
      handlePrim(node);
    }

    const children = Array.isArray(node.children) ? node.children : [];
    for (const child of children) {
      visit(child);
    }
  }

  function handlePrim(node) {
    const requiredScopes = getRequiredScopes(node, catalog, normalizedRules);
    if (requiredScopes.length === 0) {
      return;
    }

    const displayName = getPrimDisplayName(node);

    if (scopeStack.length === 0) {
      reasons.push(
        `auth: ${displayName} requires Authorize{scope in [${requiredScopes.join(', ')}]}`
      );
      return;
    }

    let matched = false;
    for (let i = scopeStack.length - 1; i >= 0; i -= 1) {
      const entry = scopeStack[i];
      const intersection = intersectScopes(entry.scopes, requiredScopes);
      if (intersection.length > 0) {
        matched = true;
        for (const scope of intersection) {
          entry.usedScopes.add(scope);
        }
        break;
      }
    }

    if (matched) {
      return;
    }

    const available = collectAvailableScopes(scopeStack);
    reasons.push(
      `auth: scope mismatch for ${displayName} (have [${available.join(', ')}], need one of [${requiredScopes.join(', ')}])`
    );
  }
}

function intersectScopes(a, b) {
  if (!Array.isArray(a) || !Array.isArray(b)) {
    return [];
  }
  const setB = new Set(b);
  const result = [];
  for (const scope of a) {
    if (setB.has(scope)) {
      result.push(scope);
    }
  }
  return result;
}

function collectAvailableScopes(stack) {
  const result = [];
  const seen = new Set();
  for (const entry of stack) {
    for (const scope of entry.scopes || []) {
      if (!seen.has(scope)) {
        seen.add(scope);
        result.push(scope);
      }
    }
  }
  return result;
}

function extractAuthorizeScopes(attrs) {
  if (!attrs || typeof attrs !== 'object') {
    return [];
  }

  const raw =
    attrs.scope !== undefined
      ? attrs.scope
      : attrs.scopes !== undefined
      ? attrs.scopes
      : [];

  if (Array.isArray(raw)) {
    return normalizeScopeList(raw);
  }

  if (typeof raw === 'string') {
    if (raw.includes(',')) {
      return normalizeScopeList(raw.split(','));
    }
    return normalizeScopeList([raw]);
  }

  return [];
}

function normalizeScopeList(list) {
  const result = [];
  const seen = new Set();
  for (const value of list || []) {
    if (typeof value !== 'string') {
      continue;
    }
    const trimmed = value.trim();
    if (!trimmed || seen.has(trimmed)) {
      continue;
    }
    seen.add(trimmed);
    result.push(trimmed);
  }
  return result;
}

function getRequiredScopes(node, catalog, rules) {
  const canonicalId = getCanonicalId(node);
  if (canonicalId) {
    const direct = rules[canonicalId];
    if (Array.isArray(direct)) {
      return normalizeScopeList(direct);
    }
    if (direct !== undefined) {
      return [];
    }
  }

  const baseName = getBaseName(node);
  if (!baseName) {
    return [];
  }

  if (!hasCryptoEffect(node, catalog)) {
    return [];
  }

  if (!PROTECTED_NAME_PATTERN.test(baseName)) {
    return [];
  }

  const fallback = findRuleScopesByBase(rules, baseName);
  if (Array.isArray(fallback)) {
    return normalizeScopeList(fallback);
  }

  return [];
}

function findRuleScopesByBase(rules, baseName) {
  const target = typeof baseName === 'string' ? baseName.toLowerCase() : '';
  if (!target) {
    return null;
  }

  for (const [key, value] of Object.entries(rules || {})) {
    if (!Array.isArray(value)) {
      continue;
    }
    const base = extractBaseNameFromId(key).toLowerCase();
    if (base === target) {
      return value;
    }
  }

  return null;
}

function getPrimDisplayName(node) {
  const canonicalId = getCanonicalId(node);
  if (canonicalId) {
    return canonicalId;
  }
  if (typeof node?.prim === 'string' && node.prim.length > 0) {
    return node.prim;
  }
  if (typeof node?.id === 'string' && node.id.length > 0) {
    return node.id;
  }
  return 'primitive';
}

function getCanonicalId(node) {
  if (!node || typeof node !== 'object') {
    return null;
  }
  const candidates = [
    node.canonical_id,
    node.canonicalId,
    node.prim_id,
    node.primId,
    node.id
  ];
  for (const value of candidates) {
    if (typeof value === 'string' && value.length > 0) {
      return value;
    }
  }
  return null;
}

function getBaseName(node) {
  const canonicalId = getCanonicalId(node);
  if (canonicalId) {
    const baseFromId = extractBaseNameFromId(canonicalId);
    if (baseFromId) {
      return baseFromId;
    }
  }

  if (typeof node?.prim === 'string' && node.prim.length > 0) {
    return node.prim;
  }

  return '';
}

function extractBaseNameFromId(id) {
  if (typeof id !== 'string' || id.length === 0) {
    return '';
  }
  const match = /\/([^/@]+)(?:@\d+)?$/.exec(id);
  if (match) {
    return match[1];
  }
  const trimmed = id.split('@')[0];
  const slash = trimmed.lastIndexOf('/');
  if (slash >= 0) {
    return trimmed.slice(slash + 1);
  }
  const colon = trimmed.lastIndexOf(':');
  if (colon >= 0) {
    return trimmed.slice(colon + 1);
  }
  return trimmed;
}

function hasCryptoEffect(node, catalog) {
  const entry = lookupCatalogEntry(node, catalog);
  const effects = Array.isArray(entry?.effects) ? entry.effects : [];
  return effects.some(
    (effect) => typeof effect === 'string' && effect.toLowerCase() === 'crypto'
  );
}

function lookupCatalogEntry(node, catalog) {
  const primitives = Array.isArray(catalog?.primitives)
    ? catalog.primitives
    : [];
  if (primitives.length === 0) {
    return null;
  }

  const canonicalId = getCanonicalId(node);
  if (canonicalId) {
    const lowered = canonicalId.toLowerCase();
    const byId = primitives.find(
      (prim) => typeof prim?.id === 'string' && prim.id.toLowerCase() === lowered
    );
    if (byId) {
      return byId;
    }
  }

  const name = typeof node?.prim === 'string' ? node.prim : '';
  if (name) {
    const loweredName = name.toLowerCase();
    const byName = primitives.find(
      (prim) => typeof prim?.name === 'string' && prim.name.toLowerCase() === loweredName
    );
    if (byName) {
      return byName;
    }

    const regex = new RegExp(`/${escapeRegex(loweredName)}@\\d+$`, 'i');
    for (const prim of primitives) {
      if (typeof prim?.id === 'string' && regex.test(prim.id)) {
        return prim;
      }
    }
  }

  if (canonicalId) {
    const base = extractBaseNameFromId(canonicalId);
    if (base) {
      const loweredBase = base.toLowerCase();
      const regex = new RegExp(`/${escapeRegex(loweredBase)}@\\d+$`, 'i');
      for (const prim of primitives) {
        if (typeof prim?.id === 'string' && regex.test(prim.id)) {
          return prim;
        }
      }
    }
  }

  return null;
}

function escapeRegex(value) {
  return value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function isObject(value) {
  return value !== null && typeof value === 'object';
}
