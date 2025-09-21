const DEFAULT_OPTS = {
  warnUnused: false,
  strictWarnsFail: false
};

const FALLBACK_SCOPE_BY_BASENAME = {
  'sign-data': ['kms.sign'],
  encrypt: ['kms.encrypt'],
  decrypt: ['kms.decrypt']
};

const SPECIAL_REGEX_CHARS = /[.*+?^${}()|[\]\\]/g;

export function checkAuthorize(ir, catalog, rules = {}, opts = {}) {
  const options = { ...DEFAULT_OPTS, ...(opts || {}) };
  const ruleMap = buildRuleMap(rules);
  const reasons = [];
  const warnings = [];
  const authorizeStack = [];

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
      const scopes = normalizeScopes(node?.attrs);
      const frame = { scopes, used: false };
      authorizeStack.push(frame);
      const children = Array.isArray(node.children) ? node.children : [];
      for (const child of children) {
        visit(child);
      }
      authorizeStack.pop();
      if (options.warnUnused && scopes.length > 0 && !frame.used) {
        for (const scope of scopes) {
          warnings.push(`auth: unused authorize scope "${scope}"`);
        }
      }
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
    const rawName = typeof node?.prim === 'string' ? node.prim : '';
    if (!rawName) {
      return;
    }

    const lowerName = rawName.toLowerCase();
    const catalogEntry = lookupCatalogPrimitive(catalog, lowerName);
    const canonicalId = catalogEntry?.id?.toLowerCase() ?? (isCanonicalId(lowerName) ? lowerName : null);
    const baseName = baseNameFromPrim(canonicalId ?? lowerName);

    let requiredScopes = ruleMap.get(canonicalId ?? '') ?? [];
    if (requiredScopes.length === 0) {
      const fallback = fallbackScopes(baseName, catalogEntry);
      if (fallback.length === 0) {
        return;
      }
      requiredScopes = fallback;
    }

    if (authorizeStack.length === 0) {
      reasons.push(`auth: ${displayPrim(canonicalId, rawName)} requires Authorize{scope in [${requiredScopes.join(', ')}]}`);
      return;
    }

    let satisfied = false;
    const collectedScopes = [];
    for (let i = authorizeStack.length - 1; i >= 0; i -= 1) {
      const frame = authorizeStack[i];
      for (const scope of frame.scopes) {
        if (!collectedScopes.includes(scope)) {
          collectedScopes.push(scope);
        }
      }
      const matches = intersectScopes(frame.scopes, requiredScopes);
      if (matches.length > 0) {
        frame.used = true;
        satisfied = true;
      }
    }

    if (!satisfied) {
      const haveList = collectedScopes.length > 0 ? collectedScopes : ['<none>'];
      reasons.push(
        `auth: scope mismatch for ${displayPrim(canonicalId, rawName)} (have [${haveList.join(', ')}], need one of [${requiredScopes.join(', ')}])`
      );
    }
  }

  visit(ir);

  const ok = reasons.length === 0 && (!options.strictWarnsFail || warnings.length === 0);

  return { ok, reasons, warnings };
}

function buildRuleMap(rules) {
  const map = new Map();
  if (rules instanceof Map) {
    for (const [key, value] of rules.entries()) {
      const scopes = normalizeScopeList(value);
      if (key) {
        map.set(String(key).toLowerCase(), scopes);
      }
    }
    return map;
  }
  const entries = rules && typeof rules === 'object' ? Object.entries(rules) : [];
  for (const [key, value] of entries) {
    if (!key) continue;
    map.set(String(key).toLowerCase(), normalizeScopeList(value));
  }
  return map;
}

function normalizeScopeList(value) {
  if (!Array.isArray(value)) {
    return [];
  }
  const out = [];
  for (const scope of value) {
    if (typeof scope === 'string' && scope.length > 0) {
      if (!out.includes(scope)) {
        out.push(scope);
      }
    }
  }
  return out;
}

function normalizeScopes(attrs = {}) {
  const source = attrs.scope ?? attrs.scopes ?? [];
  if (Array.isArray(source)) {
    return source
      .filter((value) => typeof value === 'string' && value.length > 0)
      .map((value) => value)
      .filter((value, index, arr) => arr.indexOf(value) === index);
  }
  if (typeof source === 'string') {
    return source
      .split(',')
      .map((value) => value.trim())
      .filter((value, index, arr) => value.length > 0 && arr.indexOf(value) === index);
  }
  return [];
}

function fallbackScopes(baseName, catalogEntry) {
  if (!catalogEntry) {
    return [];
  }
  const effects = Array.isArray(catalogEntry.effects) ? catalogEntry.effects : [];
  const hasCrypto = effects.some((effect) => typeof effect === 'string' && effect.toLowerCase() === 'crypto');
  if (!hasCrypto) {
    return [];
  }
  const lowerBase = baseName.toLowerCase();
  const fallback = FALLBACK_SCOPE_BY_BASENAME[lowerBase];
  if (!Array.isArray(fallback) || fallback.length === 0) {
    return [];
  }
  return fallback;
}

function intersectScopes(a = [], b = []) {
  const result = [];
  for (const scope of a) {
    if (b.includes(scope) && !result.includes(scope)) {
      result.push(scope);
    }
  }
  return result;
}

function lookupCatalogPrimitive(catalog, name) {
  const primitives = Array.isArray(catalog?.primitives) ? catalog.primitives : [];
  if (primitives.length === 0) {
    return null;
  }
  if (!name) {
    return null;
  }
  const lowerName = name.toLowerCase();
  for (const prim of primitives) {
    const id = typeof prim?.id === 'string' ? prim.id.toLowerCase() : '';
    if (id && id === lowerName) {
      return prim;
    }
  }
  for (const prim of primitives) {
    const primName = typeof prim?.name === 'string' ? prim.name.toLowerCase() : '';
    if (primName && primName === lowerName) {
      return prim;
    }
  }
  if (!lowerName.includes(':') && !lowerName.includes('/')) {
    const regex = new RegExp(`/${escapeRegex(lowerName)}@\\d+$`, 'i');
    for (const prim of primitives) {
      const id = typeof prim?.id === 'string' ? prim.id : '';
      if (id && regex.test(id)) {
        return prim;
      }
    }
  }
  return null;
}

function escapeRegex(value) {
  return value.replace(SPECIAL_REGEX_CHARS, '\\$&');
}

function baseNameFromPrim(primName = '') {
  if (!primName) {
    return '';
  }
  const afterSlash = primName.lastIndexOf('/');
  const afterColon = primName.lastIndexOf(':');
  const start = Math.max(afterSlash, afterColon);
  let base = start >= 0 ? primName.slice(start + 1) : primName;
  const at = base.indexOf('@');
  if (at >= 0) {
    base = base.slice(0, at);
  }
  return base;
}

function isCanonicalId(value) {
  return typeof value === 'string' && value.includes(':') && value.includes('/') && value.includes('@');
}

function displayPrim(canonicalId, rawName) {
  if (canonicalId) {
    return canonicalId;
  }
  return rawName;
}
